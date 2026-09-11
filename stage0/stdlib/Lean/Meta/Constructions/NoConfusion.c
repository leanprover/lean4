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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getNumHeadForalls(lean_object*);
lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2;
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18;
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
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "mkNoConfusion: unexpected equality `"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` as next argument to"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1___boxed(lean_object**);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unexpected number of level parameters in "};
static const lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___boxed(lean_object**);
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
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v_a_232_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
v___x_233_ = lean_array_fget(v_array_221_, v_start_222_);
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_start_222_, v___x_234_);
lean_dec(v_start_222_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_235_);
v___x_237_ = v___x_230_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_array_221_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_stop_223_);
v___x_237_ = v_reuseFailAlloc_280_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
lean_object* v___x_238_; 
lean_inc(v_a_232_);
v___x_238_ = l_Lean_Meta_isProof(v_a_232_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; uint8_t v___x_240_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v___x_238_, 1);
v___x_240_ = lean_unbox(v_a_239_);
lean_dec(v_a_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = l_Lean_Expr_fvarId_x21(v_a_232_);
v___x_242_ = l_Lean_FVarId_getUserName___redArg(v___x_241_, v___y_204_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__1___closed__0));
v___x_245_ = lean_name_append_after(v_a_243_, v___x_244_);
lean_inc(v_a_232_);
v___x_246_ = l_Lean_Meta_mkEqHEq(v_a_232_, v___x_233_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref_known(v___x_246_, 1);
v___x_248_ = 0;
v___x_249_ = l_Lean_mkForall(v___x_245_, v___x_248_, v_a_247_, v_fst_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_237_);
lean_ctor_set(v___x_219_, 0, v___x_249_);
v___x_251_ = v___x_219_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_237_);
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
lean_dec(v___x_245_);
lean_dec_ref(v___x_237_);
lean_del_object(v___x_219_);
lean_dec(v_fst_217_);
v_a_253_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_246_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_246_);
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
lean_dec_ref(v___x_237_);
lean_dec(v___x_233_);
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
lean_dec(v___x_233_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 1, v___x_237_);
v___x_270_ = v___x_219_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_fst_217_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_237_);
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
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec_ref(v___x_237_);
lean_dec(v___x_233_);
lean_del_object(v___x_219_);
lean_dec(v_fst_217_);
v_a_272_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_238_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_238_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
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
size_t v_sz_boxed_342_; size_t v___x_4604__boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v___x_4604__boxed_343_ = lean_unbox_usize(v___x_331_);
lean_dec(v___x_331_);
v_res_344_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0(v___x_329_, v_sz_boxed_342_, v___x_4604__boxed_343_, v___x_332_, v_xs1_333_, v_fields1_334_, v_xs2_335_, v_fields2_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
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
v___x_458_ = l_instMonadEIO___redArg();
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
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_3511__overap_520_; lean_object* v___x_521_; 
v___x_518_ = lean_box(0);
v___x_519_ = l_instInhabitedOfMonad___redArg(v___x_517_, v___x_518_);
v___x_3511__overap_520_ = lean_panic_fn_borrowed(v___x_519_, v_msg_463_);
lean_dec(v___x_519_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
v___x_521_ = lean_apply_5(v___x_3511__overap_520_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, lean_box(0));
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
lean_object* v___x_547_; lean_object* v_env_548_; lean_object* v___x_549_; lean_object* v_toCold_550_; lean_object* v_mctx_551_; lean_object* v_lctx_552_; lean_object* v_options_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_547_ = lean_st_ref_get(v___y_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = lean_st_ref_get(v___y_543_);
v_toCold_550_ = lean_ctor_get(v___y_544_, 0);
v_mctx_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_mctx_551_);
lean_dec(v___x_549_);
v_lctx_552_ = lean_ctor_get(v___y_542_, 2);
v_options_553_ = lean_ctor_get(v_toCold_550_, 2);
lean_inc_ref(v_options_553_);
lean_inc_ref(v_lctx_552_);
v___x_554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_554_, 0, v_env_548_);
lean_ctor_set(v___x_554_, 1, v_mctx_551_);
lean_ctor_set(v___x_554_, 2, v_lctx_552_);
lean_ctor_set(v___x_554_, 3, v_options_553_);
v___x_555_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
lean_ctor_set(v___x_555_, 1, v_msgData_541_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4___boxed(lean_object* v_msgData_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msgData_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(lean_object* v_msg_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_ref_570_; lean_object* v___x_571_; lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_580_; 
v_ref_570_ = lean_ctor_get(v___y_567_, 2);
v___x_571_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_580_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_580_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_578_; 
lean_inc(v_ref_570_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v_ref_570_);
lean_ctor_set(v___x_576_, 1, v_a_572_);
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 1);
lean_ctor_set(v___x_574_, 0, v___x_576_);
v___x_578_ = v___x_574_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg___boxed(lean_object* v_msg_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_587_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__0));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__2));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_597_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_598_ = lean_unsigned_to_nat(11u);
v___x_599_ = lean_unsigned_to_nat(122u);
v___x_600_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__5));
v___x_601_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__4));
v___x_602_ = l_mkPanicMessageWithDecl(v___x_601_, v___x_600_, v___x_599_, v___x_598_, v___x_597_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v___x_617_; lean_object* v_env_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_st_ref_get(v___y_607_);
v_env_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_ref(v_env_618_);
lean_dec(v___x_617_);
v___x_619_ = 0;
lean_inc(v_constName_603_);
v___x_620_ = l_Lean_Environment_findAsync_x3f(v_env_618_, v_constName_603_, v___x_619_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_val_621_; uint8_t v_kind_622_; 
v_val_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v___x_620_, 1);
v_kind_622_ = lean_ctor_get_uint8(v_val_621_, sizeof(void*)*3);
if (v_kind_622_ == 6)
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_621_);
if (lean_obj_tag(v___x_623_) == 6)
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_constName_603_);
v_val_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 0);
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_val_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v___x_623_);
v___x_632_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__7);
v___x_633_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__1(v___x_632_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_642_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_642_ == 0)
{
v___x_636_ = v___x_633_;
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_642_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
if (lean_obj_tag(v_a_634_) == 0)
{
lean_del_object(v___x_636_);
goto v___jp_609_;
}
else
{
lean_object* v_val_638_; lean_object* v___x_640_; 
lean_dec(v_constName_603_);
v_val_638_ = lean_ctor_get(v_a_634_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v_a_634_, 1);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_val_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_val_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_constName_603_);
v_a_643_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_633_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_633_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_dec(v_val_621_);
goto v___jp_609_;
}
}
else
{
lean_dec(v___x_620_);
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_610_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1);
v___x_611_ = 0;
v___x_612_ = l_Lean_MessageData_ofConstName(v_constName_603_, v___x_611_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_610_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__3);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_615_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___boxed(lean_object* v_constName_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_constName_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(lean_object* v_ctorName_658_, lean_object* v_P_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_ctorName_658_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_toConstantVal_667_; lean_object* v_numParams_668_; lean_object* v_type_669_; lean_object* v___x_670_; lean_object* v___f_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_toConstantVal_667_ = lean_ctor_get(v_a_666_, 0);
lean_inc_ref(v_toConstantVal_667_);
v_numParams_668_ = lean_ctor_get(v_a_666_, 3);
lean_inc(v_numParams_668_);
lean_dec(v_a_666_);
v_type_669_ = lean_ctor_get(v_toConstantVal_667_, 2);
lean_inc_ref_n(v_type_669_, 2);
lean_dec_ref(v_toConstantVal_667_);
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v_numParams_668_);
lean_inc_ref(v___x_670_);
v___f_671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__4___boxed), 10, 3);
lean_closure_set(v___f_671_, 0, v_P_659_);
lean_closure_set(v___f_671_, 1, v_type_669_);
lean_closure_set(v___f_671_, 2, v___x_670_);
v___x_672_ = 0;
v___x_673_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_669_, v___x_670_, v___f_671_, v___x_672_, v___x_672_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
return v___x_673_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v_P_659_);
v_a_674_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_665_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_665_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___boxed(lean_object* v_ctorName_682_, lean_object* v_P_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_ctorName_682_, v_P_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0(lean_object* v_00_u03b1_690_, lean_object* v_msg_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___boxed(lean_object* v_00_u03b1_698_, lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0(v_00_u03b1_698_, v_msg_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(lean_object* v_name_706_, lean_object* v_decl_707_, lean_object* v_ref_708_){
_start:
{
lean_object* v_defValue_710_; lean_object* v_descr_711_; lean_object* v_deprecation_x3f_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_defValue_710_ = lean_ctor_get(v_decl_707_, 0);
v_descr_711_ = lean_ctor_get(v_decl_707_, 1);
v_deprecation_x3f_712_ = lean_ctor_get(v_decl_707_, 2);
v___x_713_ = lean_alloc_ctor(1, 0, 1);
v___x_714_ = lean_unbox(v_defValue_710_);
lean_ctor_set_uint8(v___x_713_, 0, v___x_714_);
lean_inc(v_deprecation_x3f_712_);
lean_inc_ref(v_descr_711_);
lean_inc_n(v_name_706_, 2);
v___x_715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_715_, 0, v_name_706_);
lean_ctor_set(v___x_715_, 1, v_ref_708_);
lean_ctor_set(v___x_715_, 2, v___x_713_);
lean_ctor_set(v___x_715_, 3, v_descr_711_);
lean_ctor_set(v___x_715_, 4, v_deprecation_x3f_712_);
v___x_716_ = lean_register_option(v_name_706_, v___x_715_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_725_);
v___x_718_ = v___x_716_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
lean_inc(v_defValue_710_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_name_706_);
lean_ctor_set(v___x_720_, 1, v_defValue_710_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_name_706_);
v_a_726_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_716_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_716_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_734_, lean_object* v_decl_735_, lean_object* v_ref_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(v_name_734_, v_decl_735_, v_ref_736_);
lean_dec_ref(v_decl_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_784_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_));
v___x_786_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4__spec__0(v___x_783_, v___x_784_, v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4____boxed(lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_2636467839____hygCtx___hyg_4_();
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(lean_object* v_indName_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_792_ = l_Lean_Name_str___override(v_indName_790_, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(lean_object* v_opts_793_, lean_object* v_opt_794_){
_start:
{
lean_object* v_name_795_; lean_object* v_defValue_796_; lean_object* v_map_797_; lean_object* v___x_798_; 
v_name_795_ = lean_ctor_get(v_opt_794_, 0);
v_defValue_796_ = lean_ctor_get(v_opt_794_, 1);
v_map_797_ = lean_ctor_get(v_opts_793_, 0);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_797_, v_name_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
uint8_t v___x_799_; 
v___x_799_ = lean_unbox(v_defValue_796_);
return v___x_799_;
}
else
{
lean_object* v_val_800_; 
v_val_800_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v___x_798_, 1);
if (lean_obj_tag(v_val_800_) == 1)
{
uint8_t v_v_801_; 
v_v_801_ = lean_ctor_get_uint8(v_val_800_, 0);
lean_dec_ref_known(v_val_800_, 0);
return v_v_801_;
}
else
{
uint8_t v___x_802_; 
lean_dec(v_val_800_);
v___x_802_ = lean_unbox(v_defValue_796_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0___boxed(lean_object* v_opts_803_, lean_object* v_opt_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_803_, v_opt_804_);
lean_dec_ref(v_opt_804_);
lean_dec_ref(v_opts_803_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(lean_object* v_constName_807_, uint8_t v_skipRealize_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v_env_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = lean_st_ref_get(v___y_809_);
v_env_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc_ref(v_env_812_);
lean_dec(v___x_811_);
v___x_813_ = l_Lean_Environment_contains(v_env_812_, v_constName_807_, v_skipRealize_808_);
v___x_814_ = lean_box(v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg___boxed(lean_object* v_constName_816_, lean_object* v_skipRealize_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v_skipRealize_boxed_820_; lean_object* v_res_821_; 
v_skipRealize_boxed_820_ = lean_unbox(v_skipRealize_817_);
v_res_821_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v_constName_816_, v_skipRealize_boxed_820_, v___y_818_);
lean_dec(v___y_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1(lean_object* v_constName_822_, uint8_t v_skipRealize_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v_constName_822_, v_skipRealize_823_, v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___boxed(lean_object* v_constName_830_, lean_object* v_skipRealize_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v_skipRealize_boxed_837_; lean_object* v_res_838_; 
v_skipRealize_boxed_837_ = lean_unbox(v_skipRealize_831_);
v_res_838_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1(v_constName_830_, v_skipRealize_boxed_837_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear(lean_object* v_indName_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_toCold_850_; lean_object* v_options_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_toCold_850_ = lean_ctor_get(v_a_847_, 0);
v_options_851_ = lean_ctor_get(v_toCold_850_, 2);
v___x_852_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
v___x_853_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_851_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_indName_844_);
v___x_854_ = lean_box(v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_a_858_; uint8_t v___x_859_; 
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___closed__2));
v___x_857_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_856_, v___x_853_, v_a_848_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
v___x_859_ = lean_unbox(v_a_858_);
lean_dec(v_a_858_);
if (v___x_859_ == 0)
{
lean_dec(v_indName_844_);
return v___x_857_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_a_862_; uint8_t v___x_863_; 
lean_dec_ref(v___x_857_);
v___x_860_ = l_Lean_mkCtorElimName(v_indName_844_);
v___x_861_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_860_, v___x_853_, v_a_848_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
v___x_863_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
if (v___x_863_ == 0)
{
return v___x_861_;
}
else
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_861_, 0);
lean_dec(v_unused_872_);
v___x_865_ = v___x_861_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = lean_box(v___x_853_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear___boxed(lean_object* v_indName_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear(v_indName_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0(lean_object* v_then_880_, lean_object* v_h_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; 
lean_inc(v___y_885_);
lean_inc_ref(v___y_884_);
lean_inc(v___y_883_);
lean_inc_ref(v___y_882_);
lean_inc_ref(v_h_881_);
v___x_887_ = lean_apply_6(v_then_880_, v_h_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, lean_box(0));
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; uint8_t v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_889_);
v___x_891_ = lean_array_push(v___x_890_, v_h_881_);
v___x_892_ = 0;
v___x_893_ = 1;
v___x_894_ = 1;
v___x_895_ = l_Lean_Meta_mkLambdaFVars(v___x_891_, v_a_888_, v___x_892_, v___x_893_, v___x_892_, v___x_893_, v___x_894_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec_ref(v___x_891_);
return v___x_895_;
}
else
{
lean_dec_ref(v_h_881_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0___boxed(lean_object* v_then_896_, lean_object* v_h_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0(v_then_896_, v_h_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1(lean_object* v_else_904_, lean_object* v_h_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; 
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc_ref(v_h_905_);
v___x_911_ = lean_apply_6(v_else_904_, v_h_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, lean_box(0));
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; uint8_t v___x_917_; uint8_t v___x_918_; lean_object* v___x_919_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_unsigned_to_nat(1u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_array_push(v___x_914_, v_h_905_);
v___x_916_ = 0;
v___x_917_ = 1;
v___x_918_ = 1;
v___x_919_ = l_Lean_Meta_mkLambdaFVars(v___x_915_, v_a_912_, v___x_916_, v___x_917_, v___x_916_, v___x_917_, v___x_918_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec_ref(v___x_915_);
return v___x_919_;
}
else
{
lean_dec_ref(v_h_905_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1___boxed(lean_object* v_else_920_, lean_object* v_h_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1(v_else_920_, v_h_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
v___x_935_ = lean_apply_6(v_k_928_, v_b_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, lean_box(0));
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0(v_k_936_, v_b_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(lean_object* v_name_944_, uint8_t v_bi_945_, lean_object* v_type_946_, lean_object* v_k_947_, uint8_t v_kind_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___f_954_; lean_object* v___x_955_; 
v___f_954_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_954_, 0, v_k_947_);
v___x_955_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_944_, v_bi_945_, v_type_946_, v___f_954_, v_kind_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_a_964_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_955_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_955_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_972_, lean_object* v_bi_973_, lean_object* v_type_974_, lean_object* v_k_975_, lean_object* v_kind_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v_bi_boxed_982_; uint8_t v_kind_boxed_983_; lean_object* v_res_984_; 
v_bi_boxed_982_ = lean_unbox(v_bi_973_);
v_kind_boxed_983_ = lean_unbox(v_kind_976_);
v_res_984_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_972_, v_bi_boxed_982_, v_type_974_, v_k_975_, v_kind_boxed_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(lean_object* v_name_985_, lean_object* v_type_986_, lean_object* v_k_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = 0;
v___x_994_ = 0;
v___x_995_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_985_, v___x_993_, v_type_986_, v_k_987_, v___x_994_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg___boxed(lean_object* v_name_996_, lean_object* v_type_997_, lean_object* v_k_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v_name_996_, v_type_997_, v_k_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = lean_unsigned_to_nat(1u);
v___x_1008_ = l_Lean_Level_ofNat(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__1);
v___x_1011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2);
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0));
v___x_1014_ = l_Lean_mkConst(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
v___x_1019_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__5));
v___x_1020_ = l_Lean_mkConst(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = lean_box(0);
v___x_1029_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__10));
v___x_1030_ = l_Lean_mkConst(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(lean_object* v_P_1034_, lean_object* v_e1_1035_, lean_object* v_e2_1036_, lean_object* v_then_1037_, lean_object* v_else_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_heq_1049_; lean_object* v___x_1050_; 
v___f_1044_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1044_, 0, v_then_1037_);
v___f_1045_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1045_, 0, v_else_1038_);
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__3);
v___x_1048_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__6);
lean_inc_ref(v_e2_1036_);
lean_inc_ref(v_e1_1035_);
v_heq_1049_ = l_Lean_mkApp3(v___x_1047_, v___x_1048_, v_e1_1035_, v_e2_1036_);
lean_inc_ref(v_P_1034_);
v___x_1050_ = l_Lean_Meta_getLevel(v_P_1034_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__8));
v___x_1053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_a_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1046_);
v___x_1054_ = l_Lean_mkConst(v___x_1052_, v___x_1053_);
v___x_1055_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__11);
v___x_1056_ = l_Lean_mkAppB(v___x_1055_, v_e1_1035_, v_e2_1036_);
lean_inc_ref_n(v_heq_1049_, 2);
v___x_1057_ = l_Lean_mkApp3(v___x_1054_, v_P_1034_, v_heq_1049_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13));
v___x_1059_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_1058_, v_heq_1049_, v___f_1044_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = l_Lean_Expr_app___override(v___x_1057_, v_a_1060_);
v___x_1062_ = l_Lean_mkNot(v_heq_1049_);
v___x_1063_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_1058_, v___x_1062_, v___f_1045_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_Expr_app___override(v___x_1061_, v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
else
{
lean_dec_ref(v___x_1061_);
return v___x_1063_;
}
}
else
{
lean_dec_ref(v___x_1057_);
lean_dec_ref(v_heq_1049_);
lean_dec_ref(v___f_1045_);
return v___x_1059_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec_ref(v_heq_1049_);
lean_dec_ref(v___f_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v_e2_1036_);
lean_dec_ref(v_e1_1035_);
lean_dec_ref(v_P_1034_);
v_a_1073_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1050_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1050_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___boxed(lean_object* v_P_1081_, lean_object* v_e1_1082_, lean_object* v_e2_1083_, lean_object* v_then_1084_, lean_object* v_else_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(v_P_1081_, v_e1_1082_, v_e2_1083_, v_then_1084_, v_else_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0(lean_object* v_00_u03b1_1092_, lean_object* v_name_1093_, uint8_t v_bi_1094_, lean_object* v_type_1095_, lean_object* v_k_1096_, uint8_t v_kind_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___redArg(v_name_1093_, v_bi_1094_, v_type_1095_, v_k_1096_, v_kind_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1104_, lean_object* v_name_1105_, lean_object* v_bi_1106_, lean_object* v_type_1107_, lean_object* v_k_1108_, lean_object* v_kind_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v_bi_boxed_1115_; uint8_t v_kind_boxed_1116_; lean_object* v_res_1117_; 
v_bi_boxed_1115_ = lean_unbox(v_bi_1106_);
v_kind_boxed_1116_ = lean_unbox(v_kind_1109_);
v_res_1117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0(v_00_u03b1_1104_, v_name_1105_, v_bi_boxed_1115_, v_type_1107_, v_k_1108_, v_kind_boxed_1116_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0(lean_object* v_00_u03b1_1118_, lean_object* v_name_1119_, lean_object* v_type_1120_, lean_object* v_k_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v_name_1119_, v_type_1120_, v_k_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_name_1129_, lean_object* v_type_1130_, lean_object* v_k_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0(v_00_u03b1_1128_, v_name_1129_, v_type_1130_, v_k_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(lean_object* v_type_1138_, lean_object* v_k_1139_, uint8_t v_cleanupAnnotations_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___f_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___f_1146_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1146_, 0, v_k_1139_);
v___x_1147_ = 0;
v___x_1148_ = lean_box(0);
v___x_1149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1147_, v___x_1148_, v_type_1138_, v___f_1146_, v_cleanupAnnotations_1140_, v___x_1147_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1149_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1149_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg___boxed(lean_object* v_type_1166_, lean_object* v_k_1167_, lean_object* v_cleanupAnnotations_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1174_; lean_object* v_res_1175_; 
v_cleanupAnnotations_boxed_1174_ = lean_unbox(v_cleanupAnnotations_1168_);
v_res_1175_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_type_1166_, v_k_1167_, v_cleanupAnnotations_boxed_1174_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3(lean_object* v_00_u03b1_1176_, lean_object* v_type_1177_, lean_object* v_k_1178_, uint8_t v_cleanupAnnotations_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_type_1177_, v_k_1178_, v_cleanupAnnotations_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_type_1187_, lean_object* v_k_1188_, lean_object* v_cleanupAnnotations_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1195_; lean_object* v_res_1196_; 
v_cleanupAnnotations_boxed_1195_ = lean_unbox(v_cleanupAnnotations_1189_);
v_res_1196_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3(v_00_u03b1_1186_, v_type_1187_, v_k_1188_, v_cleanupAnnotations_boxed_1195_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(lean_object* v_name_1197_, lean_object* v_levelParams_1198_, lean_object* v_type_1199_, lean_object* v_value_1200_, lean_object* v_hints_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v___x_1204_; uint8_t v___y_1206_; uint8_t v___y_1213_; lean_object* v_env_1216_; uint8_t v___x_1217_; 
v___x_1204_ = lean_st_ref_get(v___y_1202_);
v_env_1216_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_ref_n(v_env_1216_, 2);
lean_dec(v___x_1204_);
v___x_1217_ = l_Lean_Environment_hasUnsafe(v_env_1216_, v_type_1199_);
if (v___x_1217_ == 0)
{
uint8_t v___x_1218_; 
v___x_1218_ = l_Lean_Environment_hasUnsafe(v_env_1216_, v_value_1200_);
v___y_1213_ = v___x_1218_;
goto v___jp_1212_;
}
else
{
lean_dec_ref(v_env_1216_);
v___y_1213_ = v___x_1217_;
goto v___jp_1212_;
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_inc(v_name_1197_);
v___x_1207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1207_, 0, v_name_1197_);
lean_ctor_set(v___x_1207_, 1, v_levelParams_1198_);
lean_ctor_set(v___x_1207_, 2, v_type_1199_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_name_1197_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1210_, 0, v___x_1207_);
lean_ctor_set(v___x_1210_, 1, v_value_1200_);
lean_ctor_set(v___x_1210_, 2, v_hints_1201_);
lean_ctor_set(v___x_1210_, 3, v___x_1209_);
lean_ctor_set_uint8(v___x_1210_, sizeof(void*)*4, v___y_1206_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
v___jp_1212_:
{
if (v___y_1213_ == 0)
{
uint8_t v___x_1214_; 
v___x_1214_ = 1;
v___y_1206_ = v___x_1214_;
goto v___jp_1205_;
}
else
{
uint8_t v___x_1215_; 
v___x_1215_ = 0;
v___y_1206_ = v___x_1215_;
goto v___jp_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg___boxed(lean_object* v_name_1219_, lean_object* v_levelParams_1220_, lean_object* v_type_1221_, lean_object* v_value_1222_, lean_object* v_hints_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_name_1219_, v_levelParams_1220_, v_type_1221_, v_value_1222_, v_hints_1223_, v___y_1224_);
lean_dec(v___y_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6(lean_object* v_name_1227_, lean_object* v_levelParams_1228_, lean_object* v_type_1229_, lean_object* v_value_1230_, lean_object* v_hints_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_name_1227_, v_levelParams_1228_, v_type_1229_, v_value_1230_, v_hints_1231_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___boxed(lean_object* v_name_1238_, lean_object* v_levelParams_1239_, lean_object* v_type_1240_, lean_object* v_value_1241_, lean_object* v_hints_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6(v_name_1238_, v_levelParams_1239_, v_type_1240_, v_value_1241_, v_hints_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___f_1256_; lean_object* v___x_13648__overap_1257_; lean_object* v___x_1258_; 
v___f_1256_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_13648__overap_1257_ = lean_panic_fn_borrowed(v___f_1256_, v_msg_1250_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
v___x_1258_ = lean_apply_5(v___x_13648__overap_1257_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, lean_box(0));
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___boxed(lean_object* v_msg_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v_msg_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(lean_object* v___x_1266_, uint8_t v___x_1267_, lean_object* v_ys_1268_, lean_object* v_x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_1275_; uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = 0;
v___x_1276_ = 1;
v___x_1277_ = l_Lean_Meta_mkLambdaFVars(v_ys_1268_, v___x_1266_, v___x_1275_, v___x_1267_, v___x_1275_, v___x_1267_, v___x_1276_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed(lean_object* v___x_1278_, lean_object* v___x_1279_, lean_object* v_ys_1280_, lean_object* v_x_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v___x_16251__boxed_1287_; lean_object* v_res_1288_; 
v___x_16251__boxed_1287_ = lean_unbox(v___x_1279_);
v_res_1288_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(v___x_1278_, v___x_16251__boxed_1287_, v_ys_1280_, v_x_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_x_1281_);
lean_dec_ref(v_ys_1280_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object* v_P_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_P_1289_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object* v_P_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(v_P_1297_, v_x_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec_ref(v_x_1298_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object* v___x_1305_, lean_object* v_P_1306_, lean_object* v_xs1_1307_, lean_object* v_zs1_1308_, lean_object* v_xs2_1309_, uint8_t v___x_1310_, uint8_t v___x_1311_, lean_object* v_zs2_1312_, lean_object* v_x_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
lean_inc_ref(v_P_1306_);
v___x_1319_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1305_, v_P_1306_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = l_Array_append___redArg(v_xs1_1307_, v_zs1_1308_);
v___x_1322_ = l_Array_append___redArg(v___x_1321_, v_xs2_1309_);
v___x_1323_ = l_Array_append___redArg(v___x_1322_, v_zs2_1312_);
v___x_1324_ = l_Lean_Expr_beta(v_a_1320_, v___x_1323_);
v___x_1325_ = l_Lean_mkArrow(v___x_1324_, v_P_1306_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; uint8_t v___x_1327_; lean_object* v___x_1328_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = 1;
v___x_1328_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1312_, v_a_1326_, v___x_1310_, v___x_1311_, v___x_1310_, v___x_1311_, v___x_1327_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1328_;
}
else
{
return v___x_1325_;
}
}
else
{
lean_dec_ref(v_xs1_1307_);
lean_dec_ref(v_P_1306_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object* v___x_1329_, lean_object* v_P_1330_, lean_object* v_xs1_1331_, lean_object* v_zs1_1332_, lean_object* v_xs2_1333_, lean_object* v___x_1334_, lean_object* v___x_1335_, lean_object* v_zs2_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
uint8_t v___x_16301__boxed_1343_; uint8_t v___x_16302__boxed_1344_; lean_object* v_res_1345_; 
v___x_16301__boxed_1343_ = lean_unbox(v___x_1334_);
v___x_16302__boxed_1344_ = lean_unbox(v___x_1335_);
v_res_1345_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(v___x_1329_, v_P_1330_, v_xs1_1331_, v_zs1_1332_, v_xs2_1333_, v___x_16301__boxed_1343_, v___x_16302__boxed_1344_, v_zs2_1336_, v_x_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v_x_1337_);
lean_dec_ref(v_zs2_1336_);
lean_dec_ref(v_xs2_1333_);
lean_dec_ref(v_zs1_1332_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object* v_val_1346_, lean_object* v___x_1347_, lean_object* v___x_1348_, lean_object* v_P_1349_, lean_object* v_xs1_1350_, lean_object* v_zs1_1351_, lean_object* v_xs2_1352_, uint8_t v___x_1353_, uint8_t v___x_1354_, lean_object* v_indName_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v_ysx2_1358_, lean_object* v_h_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_ctors_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v_ctors_1365_ = lean_ctor_get(v_val_1346_, 4);
v___x_1366_ = l_List_get_x21Internal___redArg(v___x_1347_, v_ctors_1365_, v___x_1348_);
v___x_1367_ = lean_box(v___x_1353_);
v___x_1368_ = lean_box(v___x_1354_);
lean_inc_ref(v_xs2_1352_);
lean_inc(v___x_1366_);
v___f_1369_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1369_, 0, v___x_1366_);
lean_closure_set(v___f_1369_, 1, v_P_1349_);
lean_closure_set(v___f_1369_, 2, v_xs1_1350_);
lean_closure_set(v___f_1369_, 3, v_zs1_1351_);
lean_closure_set(v___f_1369_, 4, v_xs2_1352_);
lean_closure_set(v___f_1369_, 5, v___x_1367_);
lean_closure_set(v___f_1369_, 6, v___x_1368_);
v___x_1370_ = l_Lean_mkConstructorElimName(v_indName_1355_, v___x_1366_);
v___x_1371_ = l_Lean_mkConst(v___x_1370_, v___x_1356_);
v___x_1372_ = l_Array_append___redArg(v_xs2_1352_, v___x_1357_);
v___x_1373_ = l_Array_append___redArg(v___x_1372_, v_ysx2_1358_);
v___x_1374_ = lean_unsigned_to_nat(1u);
v___x_1375_ = lean_mk_empty_array_with_capacity(v___x_1374_);
v___x_1376_ = lean_array_push(v___x_1375_, v_h_1359_);
v___x_1377_ = l_Array_append___redArg(v___x_1373_, v___x_1376_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l_Lean_mkAppN(v___x_1371_, v___x_1377_);
lean_dec_ref(v___x_1377_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc_ref(v___x_1378_);
v___x_1379_ = lean_infer_type(v___x_1378_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v___x_1379_, 1);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
v___x_1381_ = lean_whnf(v_a_1380_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Lean_Expr_bindingDomain_x21(v_a_1382_);
lean_dec(v_a_1382_);
v___x_1384_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v___x_1383_, v___f_1369_, v___x_1353_, v___x_1353_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1393_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1393_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lean_Expr_app___override(v___x_1378_, v_a_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1389_);
v___x_1391_ = v___x_1387_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
else
{
lean_dec_ref(v___x_1378_);
return v___x_1384_;
}
}
else
{
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___f_1369_);
return v___x_1381_;
}
}
else
{
lean_dec_ref(v___x_1378_);
lean_dec_ref(v___f_1369_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_val_1394_ = _args[0];
lean_object* v___x_1395_ = _args[1];
lean_object* v___x_1396_ = _args[2];
lean_object* v_P_1397_ = _args[3];
lean_object* v_xs1_1398_ = _args[4];
lean_object* v_zs1_1399_ = _args[5];
lean_object* v_xs2_1400_ = _args[6];
lean_object* v___x_1401_ = _args[7];
lean_object* v___x_1402_ = _args[8];
lean_object* v_indName_1403_ = _args[9];
lean_object* v___x_1404_ = _args[10];
lean_object* v___x_1405_ = _args[11];
lean_object* v_ysx2_1406_ = _args[12];
lean_object* v_h_1407_ = _args[13];
lean_object* v___y_1408_ = _args[14];
lean_object* v___y_1409_ = _args[15];
lean_object* v___y_1410_ = _args[16];
lean_object* v___y_1411_ = _args[17];
lean_object* v___y_1412_ = _args[18];
_start:
{
uint8_t v___x_16352__boxed_1413_; uint8_t v___x_16353__boxed_1414_; lean_object* v_res_1415_; 
v___x_16352__boxed_1413_ = lean_unbox(v___x_1401_);
v___x_16353__boxed_1414_ = lean_unbox(v___x_1402_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(v_val_1394_, v___x_1395_, v___x_1396_, v_P_1397_, v_xs1_1398_, v_zs1_1399_, v_xs2_1400_, v___x_16352__boxed_1413_, v___x_16353__boxed_1414_, v_indName_1403_, v___x_1404_, v___x_1405_, v_ysx2_1406_, v_h_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v_ysx2_1406_);
lean_dec_ref(v___x_1405_);
lean_dec(v_indName_1403_);
lean_dec(v___x_1395_);
lean_dec_ref(v_val_1394_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(uint8_t v___x_1416_, lean_object* v_P_1417_, uint8_t v___x_1418_, uint8_t v___x_1419_, lean_object* v___x_1420_, lean_object* v_xs1_1421_, lean_object* v_zs1_1422_, lean_object* v_xs2_1423_, lean_object* v_zs2_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
if (v___x_1416_ == 0)
{
uint8_t v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v_xs1_1421_);
lean_dec(v___x_1420_);
v___x_1431_ = 1;
v___x_1432_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1424_, v_P_1417_, v___x_1418_, v___x_1419_, v___x_1418_, v___x_1419_, v___x_1431_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
lean_inc_ref(v_P_1417_);
v___x_1433_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1420_, v_P_1417_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = l_Array_append___redArg(v_xs1_1421_, v_zs1_1422_);
v___x_1436_ = l_Array_append___redArg(v___x_1435_, v_xs2_1423_);
v___x_1437_ = l_Array_append___redArg(v___x_1436_, v_zs2_1424_);
v___x_1438_ = l_Lean_Expr_beta(v_a_1434_, v___x_1437_);
v___x_1439_ = l_Lean_mkArrow(v___x_1438_, v_P_1417_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1439_, 1);
v___x_1441_ = 1;
v___x_1442_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1424_, v_a_1440_, v___x_1418_, v___x_1419_, v___x_1418_, v___x_1419_, v___x_1441_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1442_;
}
else
{
return v___x_1439_;
}
}
else
{
lean_dec_ref(v_xs1_1421_);
lean_dec_ref(v_P_1417_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed(lean_object* v___x_1443_, lean_object* v_P_1444_, lean_object* v___x_1445_, lean_object* v___x_1446_, lean_object* v___x_1447_, lean_object* v_xs1_1448_, lean_object* v_zs1_1449_, lean_object* v_xs2_1450_, lean_object* v_zs2_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v___x_16444__boxed_1458_; uint8_t v___x_16445__boxed_1459_; uint8_t v___x_16446__boxed_1460_; lean_object* v_res_1461_; 
v___x_16444__boxed_1458_ = lean_unbox(v___x_1443_);
v___x_16445__boxed_1459_ = lean_unbox(v___x_1445_);
v___x_16446__boxed_1460_ = lean_unbox(v___x_1446_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(v___x_16444__boxed_1458_, v_P_1444_, v___x_16445__boxed_1459_, v___x_16446__boxed_1460_, v___x_1447_, v_xs1_1448_, v_zs1_1449_, v_xs2_1450_, v_zs2_1451_, v_x_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec_ref(v_x_1452_);
lean_dec_ref(v_zs2_1451_);
lean_dec_ref(v_xs2_1450_);
lean_dec_ref(v_zs1_1449_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(lean_object* v_i_1462_, lean_object* v_P_1463_, lean_object* v___x_1464_, lean_object* v_xs1_1465_, lean_object* v_zs1_1466_, lean_object* v_xs2_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_bs_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v_xs2_1467_);
lean_dec_ref(v_zs1_1466_);
lean_dec_ref(v_xs1_1465_);
lean_dec(v___x_1464_);
lean_dec_ref(v_P_1463_);
v___x_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_bs_1470_);
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; lean_object* v_v_1479_; lean_object* v___x_1480_; lean_object* v_bs_x27_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; 
v___x_1478_ = 0;
v_v_1479_ = lean_array_uget(v_bs_1470_, v_i_1469_);
v___x_1480_ = lean_unsigned_to_nat(0u);
v_bs_x27_1481_ = lean_array_uset(v_bs_1470_, v_i_1469_, v___x_1480_);
v___x_1482_ = lean_usize_to_nat(v_i_1469_);
v___x_1483_ = lean_nat_dec_eq(v_i_1462_, v___x_1482_);
lean_dec(v___x_1482_);
v___x_1484_ = lean_box(v___x_1483_);
v___x_1485_ = lean_box(v___x_1478_);
v___x_1486_ = lean_box(v___x_1476_);
lean_inc_ref(v_xs2_1467_);
lean_inc_ref(v_zs1_1466_);
lean_inc_ref(v_xs1_1465_);
lean_inc(v___x_1464_);
lean_inc_ref(v_P_1463_);
v___f_1487_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1487_, 0, v___x_1484_);
lean_closure_set(v___f_1487_, 1, v_P_1463_);
lean_closure_set(v___f_1487_, 2, v___x_1485_);
lean_closure_set(v___f_1487_, 3, v___x_1486_);
lean_closure_set(v___f_1487_, 4, v___x_1464_);
lean_closure_set(v___f_1487_, 5, v_xs1_1465_);
lean_closure_set(v___f_1487_, 6, v_zs1_1466_);
lean_closure_set(v___f_1487_, 7, v_xs2_1467_);
v___x_1488_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_v_1479_, v___f_1487_, v___x_1478_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; size_t v___x_1490_; size_t v___x_1491_; lean_object* v___x_1492_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1469_, v___x_1490_);
v___x_1492_ = lean_array_uset(v_bs_x27_1481_, v_i_1469_, v_a_1489_);
v_i_1469_ = v___x_1491_;
v_bs_1470_ = v___x_1492_;
goto _start;
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_bs_x27_1481_);
lean_dec_ref(v_xs2_1467_);
lean_dec_ref(v_zs1_1466_);
lean_dec_ref(v_xs1_1465_);
lean_dec(v___x_1464_);
lean_dec_ref(v_P_1463_);
v_a_1494_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1488_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1488_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___boxed(lean_object* v_i_1502_, lean_object* v_P_1503_, lean_object* v___x_1504_, lean_object* v_xs1_1505_, lean_object* v_zs1_1506_, lean_object* v_xs2_1507_, lean_object* v_sz_1508_, lean_object* v_i_1509_, lean_object* v_bs_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1508_);
lean_dec(v_sz_1508_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1509_);
lean_dec(v_i_1509_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_1502_, v_P_1503_, v___x_1504_, v_xs1_1505_, v_zs1_1506_, v_xs2_1507_, v_sz_boxed_1516_, v_i_boxed_1517_, v_bs_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v_i_1502_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(uint8_t v___y_1519_, lean_object* v_val_1520_, lean_object* v___x_1521_, lean_object* v___x_1522_, lean_object* v_xs2_1523_, lean_object* v___x_1524_, lean_object* v_ysx2_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_P_1528_, lean_object* v_xs1_1529_, uint8_t v___x_1530_, uint8_t v___x_1531_, lean_object* v_indName_1532_, lean_object* v___x_1533_, lean_object* v_tail_1534_, lean_object* v___x_1535_, lean_object* v___f_1536_, lean_object* v_zs1_1537_, lean_object* v_x_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
if (v___y_1519_ == 0)
{
lean_object* v_ctors_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v___f_1536_);
lean_dec_ref(v___x_1535_);
lean_dec(v_tail_1534_);
lean_dec(v___x_1533_);
lean_dec(v_indName_1532_);
v_ctors_1544_ = lean_ctor_get(v_val_1520_, 4);
lean_inc(v_ctors_1544_);
lean_dec_ref(v_val_1520_);
lean_inc(v___x_1522_);
v___x_1545_ = l_List_get_x21Internal___redArg(v___x_1521_, v_ctors_1544_, v___x_1522_);
lean_dec(v_ctors_1544_);
lean_dec(v___x_1521_);
lean_inc_ref(v_xs2_1523_);
v___x_1546_ = l_Array_append___redArg(v_xs2_1523_, v___x_1524_);
lean_dec_ref(v___x_1524_);
v___x_1547_ = l_Array_append___redArg(v___x_1546_, v_ysx2_1525_);
lean_dec_ref(v_ysx2_1525_);
v___x_1548_ = l_Lean_mkAppN(v___x_1526_, v___x_1547_);
lean_dec_ref(v___x_1547_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
lean_inc_ref(v___x_1548_);
v___x_1549_ = lean_infer_type(v___x_1548_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref_known(v___x_1549_, 1);
v___x_1551_ = l_Lean_Meta_arrowDomainsN(v___x_1527_, v_a_1550_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; size_t v_sz_1553_; size_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v_sz_1553_ = lean_array_size(v_a_1552_);
v___x_1554_ = ((size_t)0ULL);
lean_inc_ref(v_zs1_1537_);
v___x_1555_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v___x_1522_, v_P_1528_, v___x_1545_, v_xs1_1529_, v_zs1_1537_, v_xs2_1523_, v_sz_1553_, v___x_1554_, v_a_1552_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___x_1522_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = l_Lean_mkAppN(v___x_1548_, v_a_1556_);
lean_dec(v_a_1556_);
v___x_1558_ = 1;
v___x_1559_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1537_, v___x_1557_, v___x_1530_, v___x_1531_, v___x_1530_, v___x_1531_, v___x_1558_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v_zs1_1537_);
return v___x_1559_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v___x_1548_);
lean_dec_ref(v_zs1_1537_);
v_a_1560_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1555_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1555_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v___x_1548_);
lean_dec(v___x_1545_);
lean_dec_ref(v_zs1_1537_);
lean_dec_ref(v_xs1_1529_);
lean_dec_ref(v_P_1528_);
lean_dec_ref(v_xs2_1523_);
lean_dec(v___x_1522_);
v_a_1568_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1551_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1551_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
else
{
lean_dec_ref(v___x_1548_);
lean_dec(v___x_1545_);
lean_dec_ref(v_zs1_1537_);
lean_dec_ref(v_xs1_1529_);
lean_dec_ref(v_P_1528_);
lean_dec(v___x_1527_);
lean_dec_ref(v_xs2_1523_);
lean_dec(v___x_1522_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec(v___x_1527_);
lean_dec_ref(v___x_1526_);
v___x_1576_ = lean_box(v___x_1530_);
v___x_1577_ = lean_box(v___x_1531_);
lean_inc_ref(v_ysx2_1525_);
lean_inc(v_indName_1532_);
lean_inc_ref(v_xs2_1523_);
lean_inc_ref(v_zs1_1537_);
lean_inc(v___x_1522_);
v___f_1578_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed), 19, 13);
lean_closure_set(v___f_1578_, 0, v_val_1520_);
lean_closure_set(v___f_1578_, 1, v___x_1521_);
lean_closure_set(v___f_1578_, 2, v___x_1522_);
lean_closure_set(v___f_1578_, 3, v_P_1528_);
lean_closure_set(v___f_1578_, 4, v_xs1_1529_);
lean_closure_set(v___f_1578_, 5, v_zs1_1537_);
lean_closure_set(v___f_1578_, 6, v_xs2_1523_);
lean_closure_set(v___f_1578_, 7, v___x_1576_);
lean_closure_set(v___f_1578_, 8, v___x_1577_);
lean_closure_set(v___f_1578_, 9, v_indName_1532_);
lean_closure_set(v___f_1578_, 10, v___x_1533_);
lean_closure_set(v___f_1578_, 11, v___x_1524_);
lean_closure_set(v___f_1578_, 12, v_ysx2_1525_);
v___x_1579_ = l_Lean_mkCtorIdxName(v_indName_1532_);
v___x_1580_ = l_Lean_mkConst(v___x_1579_, v_tail_1534_);
v___x_1581_ = l_Array_append___redArg(v_xs2_1523_, v_ysx2_1525_);
lean_dec_ref(v_ysx2_1525_);
v___x_1582_ = l_Lean_mkAppN(v___x_1580_, v___x_1581_);
lean_dec_ref(v___x_1581_);
v___x_1583_ = l_Lean_mkRawNatLit(v___x_1522_);
v___x_1584_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(v___x_1535_, v___x_1582_, v___x_1583_, v___f_1578_, v___f_1536_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v___x_1586_; lean_object* v___x_1587_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = 1;
v___x_1587_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1537_, v_a_1585_, v___x_1530_, v___x_1531_, v___x_1530_, v___x_1531_, v___x_1586_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v_zs1_1537_);
return v___x_1587_;
}
else
{
lean_dec_ref(v_zs1_1537_);
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___y_1588_ = _args[0];
lean_object* v_val_1589_ = _args[1];
lean_object* v___x_1590_ = _args[2];
lean_object* v___x_1591_ = _args[3];
lean_object* v_xs2_1592_ = _args[4];
lean_object* v___x_1593_ = _args[5];
lean_object* v_ysx2_1594_ = _args[6];
lean_object* v___x_1595_ = _args[7];
lean_object* v___x_1596_ = _args[8];
lean_object* v_P_1597_ = _args[9];
lean_object* v_xs1_1598_ = _args[10];
lean_object* v___x_1599_ = _args[11];
lean_object* v___x_1600_ = _args[12];
lean_object* v_indName_1601_ = _args[13];
lean_object* v___x_1602_ = _args[14];
lean_object* v_tail_1603_ = _args[15];
lean_object* v___x_1604_ = _args[16];
lean_object* v___f_1605_ = _args[17];
lean_object* v_zs1_1606_ = _args[18];
lean_object* v_x_1607_ = _args[19];
lean_object* v___y_1608_ = _args[20];
lean_object* v___y_1609_ = _args[21];
lean_object* v___y_1610_ = _args[22];
lean_object* v___y_1611_ = _args[23];
lean_object* v___y_1612_ = _args[24];
_start:
{
uint8_t v___y_16566__boxed_1613_; uint8_t v___x_16573__boxed_1614_; uint8_t v___x_16574__boxed_1615_; lean_object* v_res_1616_; 
v___y_16566__boxed_1613_ = lean_unbox(v___y_1588_);
v___x_16573__boxed_1614_ = lean_unbox(v___x_1599_);
v___x_16574__boxed_1615_ = lean_unbox(v___x_1600_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(v___y_16566__boxed_1613_, v_val_1589_, v___x_1590_, v___x_1591_, v_xs2_1592_, v___x_1593_, v_ysx2_1594_, v___x_1595_, v___x_1596_, v_P_1597_, v_xs1_1598_, v___x_16573__boxed_1614_, v___x_16574__boxed_1615_, v_indName_1601_, v___x_1602_, v_tail_1603_, v___x_1604_, v___f_1605_, v_zs1_1606_, v_x_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec_ref(v_x_1607_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(lean_object* v_val_1617_, lean_object* v_P_1618_, lean_object* v_xs1_1619_, lean_object* v_xs2_1620_, lean_object* v_indName_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v_ysx2_1624_, uint8_t v___y_1625_, lean_object* v___x_1626_, lean_object* v___x_1627_, lean_object* v_tail_1628_, lean_object* v___x_1629_, size_t v_sz_1630_, size_t v_i_1631_, lean_object* v_bs_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_usize_dec_lt(v_i_1631_, v_sz_1630_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec_ref(v___x_1629_);
lean_dec(v_tail_1628_);
lean_dec(v___x_1627_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v_ysx2_1624_);
lean_dec_ref(v___x_1623_);
lean_dec(v___x_1622_);
lean_dec(v_indName_1621_);
lean_dec_ref(v_xs2_1620_);
lean_dec_ref(v_xs1_1619_);
lean_dec_ref(v_P_1618_);
lean_dec_ref(v_val_1617_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_bs_1632_);
return v___x_1639_;
}
else
{
lean_object* v___f_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; lean_object* v_v_1643_; lean_object* v___x_1644_; lean_object* v_bs_x27_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; 
lean_inc_ref_n(v_P_1618_, 2);
v___f_1640_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1640_, 0, v_P_1618_);
v___x_1641_ = lean_box(0);
v___x_1642_ = 0;
v_v_1643_ = lean_array_uget(v_bs_1632_, v_i_1631_);
v___x_1644_ = lean_unsigned_to_nat(0u);
v_bs_x27_1645_ = lean_array_uset(v_bs_1632_, v_i_1631_, v___x_1644_);
v___x_1646_ = lean_usize_to_nat(v_i_1631_);
v___x_1647_ = lean_box(v___y_1625_);
v___x_1648_ = lean_box(v___x_1642_);
v___x_1649_ = lean_box(v___x_1638_);
lean_inc_ref(v___x_1629_);
lean_inc(v_tail_1628_);
lean_inc(v___x_1622_);
lean_inc(v_indName_1621_);
lean_inc_ref(v_xs1_1619_);
lean_inc(v___x_1627_);
lean_inc_ref(v___x_1626_);
lean_inc_ref(v_ysx2_1624_);
lean_inc_ref(v___x_1623_);
lean_inc_ref(v_xs2_1620_);
lean_inc_ref(v_val_1617_);
v___f_1650_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1650_, 0, v___x_1647_);
lean_closure_set(v___f_1650_, 1, v_val_1617_);
lean_closure_set(v___f_1650_, 2, v___x_1641_);
lean_closure_set(v___f_1650_, 3, v___x_1646_);
lean_closure_set(v___f_1650_, 4, v_xs2_1620_);
lean_closure_set(v___f_1650_, 5, v___x_1623_);
lean_closure_set(v___f_1650_, 6, v_ysx2_1624_);
lean_closure_set(v___f_1650_, 7, v___x_1626_);
lean_closure_set(v___f_1650_, 8, v___x_1627_);
lean_closure_set(v___f_1650_, 9, v_P_1618_);
lean_closure_set(v___f_1650_, 10, v_xs1_1619_);
lean_closure_set(v___f_1650_, 11, v___x_1648_);
lean_closure_set(v___f_1650_, 12, v___x_1649_);
lean_closure_set(v___f_1650_, 13, v_indName_1621_);
lean_closure_set(v___f_1650_, 14, v___x_1622_);
lean_closure_set(v___f_1650_, 15, v_tail_1628_);
lean_closure_set(v___f_1650_, 16, v___x_1629_);
lean_closure_set(v___f_1650_, 17, v___f_1640_);
v___x_1651_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v_v_1643_, v___f_1650_, v___x_1642_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; size_t v___x_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = ((size_t)1ULL);
v___x_1654_ = lean_usize_add(v_i_1631_, v___x_1653_);
v___x_1655_ = lean_array_uset(v_bs_x27_1645_, v_i_1631_, v_a_1652_);
v_i_1631_ = v___x_1654_;
v_bs_1632_ = v___x_1655_;
goto _start;
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_bs_x27_1645_);
lean_dec_ref(v___x_1629_);
lean_dec(v_tail_1628_);
lean_dec(v___x_1627_);
lean_dec_ref(v___x_1626_);
lean_dec_ref(v_ysx2_1624_);
lean_dec_ref(v___x_1623_);
lean_dec(v___x_1622_);
lean_dec(v_indName_1621_);
lean_dec_ref(v_xs2_1620_);
lean_dec_ref(v_xs1_1619_);
lean_dec_ref(v_P_1618_);
lean_dec_ref(v_val_1617_);
v_a_1657_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1651_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1651_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_val_1665_ = _args[0];
lean_object* v_P_1666_ = _args[1];
lean_object* v_xs1_1667_ = _args[2];
lean_object* v_xs2_1668_ = _args[3];
lean_object* v_indName_1669_ = _args[4];
lean_object* v___x_1670_ = _args[5];
lean_object* v___x_1671_ = _args[6];
lean_object* v_ysx2_1672_ = _args[7];
lean_object* v___y_1673_ = _args[8];
lean_object* v___x_1674_ = _args[9];
lean_object* v___x_1675_ = _args[10];
lean_object* v_tail_1676_ = _args[11];
lean_object* v___x_1677_ = _args[12];
lean_object* v_sz_1678_ = _args[13];
lean_object* v_i_1679_ = _args[14];
lean_object* v_bs_1680_ = _args[15];
lean_object* v___y_1681_ = _args[16];
lean_object* v___y_1682_ = _args[17];
lean_object* v___y_1683_ = _args[18];
lean_object* v___y_1684_ = _args[19];
lean_object* v___y_1685_ = _args[20];
_start:
{
uint8_t v___y_16712__boxed_1686_; size_t v_sz_boxed_1687_; size_t v_i_boxed_1688_; lean_object* v_res_1689_; 
v___y_16712__boxed_1686_ = lean_unbox(v___y_1673_);
v_sz_boxed_1687_ = lean_unbox_usize(v_sz_1678_);
lean_dec(v_sz_1678_);
v_i_boxed_1688_ = lean_unbox_usize(v_i_1679_);
lean_dec(v_i_1679_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1665_, v_P_1666_, v_xs1_1667_, v_xs2_1668_, v_indName_1669_, v___x_1670_, v___x_1671_, v_ysx2_1672_, v___y_16712__boxed_1686_, v___x_1674_, v___x_1675_, v_tail_1676_, v___x_1677_, v_sz_boxed_1687_, v_i_boxed_1688_, v_bs_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(lean_object* v___x_1690_, lean_object* v_t1_1691_, lean_object* v_val_1692_, lean_object* v_P_1693_, lean_object* v_xs1_1694_, lean_object* v_xs2_1695_, lean_object* v_indName_1696_, lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v_ysx2_1699_, uint8_t v___y_1700_, lean_object* v___x_1701_, lean_object* v_tail_1702_, lean_object* v___x_1703_, lean_object* v___x_1704_, lean_object* v___x_1705_, lean_object* v_ysx1_1706_, uint8_t v___x_1707_, uint8_t v___x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
lean_inc(v___x_1690_);
v___x_1714_ = l_Lean_Meta_arrowDomainsN(v___x_1690_, v_t1_1691_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; size_t v_sz_1716_; size_t v___x_1717_; lean_object* v___x_1718_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v_sz_1716_ = lean_array_size(v_a_1715_);
v___x_1717_ = ((size_t)0ULL);
lean_inc_ref(v_ysx2_1699_);
lean_inc_ref(v_xs2_1695_);
lean_inc_ref(v_xs1_1694_);
lean_inc_ref(v_P_1693_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1692_, v_P_1693_, v_xs1_1694_, v_xs2_1695_, v_indName_1696_, v___x_1697_, v___x_1698_, v_ysx2_1699_, v___y_1700_, v___x_1701_, v___x_1690_, v_tail_1702_, v___x_1703_, v_sz_1716_, v___x_1717_, v_a_1715_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_mkAppN(v___x_1704_, v_a_1719_);
lean_dec(v_a_1719_);
v___x_1721_ = lean_array_push(v___x_1705_, v_P_1693_);
v___x_1722_ = l_Array_append___redArg(v___x_1721_, v_xs1_1694_);
lean_dec_ref(v_xs1_1694_);
v___x_1723_ = l_Array_append___redArg(v___x_1722_, v_ysx1_1706_);
v___x_1724_ = l_Array_append___redArg(v___x_1723_, v_xs2_1695_);
lean_dec_ref(v_xs2_1695_);
v___x_1725_ = l_Array_append___redArg(v___x_1724_, v_ysx2_1699_);
lean_dec_ref(v_ysx2_1699_);
v___x_1726_ = 1;
v___x_1727_ = l_Lean_Meta_mkLambdaFVars(v___x_1725_, v___x_1720_, v___x_1707_, v___x_1708_, v___x_1707_, v___x_1708_, v___x_1726_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec_ref(v___x_1725_);
return v___x_1727_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1704_);
lean_dec_ref(v_ysx2_1699_);
lean_dec_ref(v_xs2_1695_);
lean_dec_ref(v_xs1_1694_);
lean_dec_ref(v_P_1693_);
v_a_1728_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1718_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1704_);
lean_dec_ref(v___x_1703_);
lean_dec(v_tail_1702_);
lean_dec_ref(v___x_1701_);
lean_dec_ref(v_ysx2_1699_);
lean_dec_ref(v___x_1698_);
lean_dec(v___x_1697_);
lean_dec(v_indName_1696_);
lean_dec_ref(v_xs2_1695_);
lean_dec_ref(v_xs1_1694_);
lean_dec_ref(v_P_1693_);
lean_dec_ref(v_val_1692_);
lean_dec(v___x_1690_);
v_a_1736_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1714_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1714_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed(lean_object** _args){
lean_object* v___x_1744_ = _args[0];
lean_object* v_t1_1745_ = _args[1];
lean_object* v_val_1746_ = _args[2];
lean_object* v_P_1747_ = _args[3];
lean_object* v_xs1_1748_ = _args[4];
lean_object* v_xs2_1749_ = _args[5];
lean_object* v_indName_1750_ = _args[6];
lean_object* v___x_1751_ = _args[7];
lean_object* v___x_1752_ = _args[8];
lean_object* v_ysx2_1753_ = _args[9];
lean_object* v___y_1754_ = _args[10];
lean_object* v___x_1755_ = _args[11];
lean_object* v_tail_1756_ = _args[12];
lean_object* v___x_1757_ = _args[13];
lean_object* v___x_1758_ = _args[14];
lean_object* v___x_1759_ = _args[15];
lean_object* v_ysx1_1760_ = _args[16];
lean_object* v___x_1761_ = _args[17];
lean_object* v___x_1762_ = _args[18];
lean_object* v___y_1763_ = _args[19];
lean_object* v___y_1764_ = _args[20];
lean_object* v___y_1765_ = _args[21];
lean_object* v___y_1766_ = _args[22];
lean_object* v___y_1767_ = _args[23];
_start:
{
uint8_t v___y_16802__boxed_1768_; uint8_t v___x_16808__boxed_1769_; uint8_t v___x_16809__boxed_1770_; lean_object* v_res_1771_; 
v___y_16802__boxed_1768_ = lean_unbox(v___y_1754_);
v___x_16808__boxed_1769_ = lean_unbox(v___x_1761_);
v___x_16809__boxed_1770_ = lean_unbox(v___x_1762_);
v_res_1771_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(v___x_1744_, v_t1_1745_, v_val_1746_, v_P_1747_, v_xs1_1748_, v_xs2_1749_, v_indName_1750_, v___x_1751_, v___x_1752_, v_ysx2_1753_, v___y_16802__boxed_1768_, v___x_1755_, v_tail_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v_ysx1_1760_, v___x_16808__boxed_1769_, v___x_16809__boxed_1770_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec_ref(v_ysx1_1760_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(lean_object* v___x_1772_, lean_object* v_ysx1_1773_, lean_object* v___x_1774_, lean_object* v_t1_1775_, lean_object* v_val_1776_, lean_object* v_P_1777_, lean_object* v_xs1_1778_, lean_object* v_xs2_1779_, lean_object* v_indName_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, uint8_t v___y_1783_, lean_object* v___x_1784_, lean_object* v_tail_1785_, lean_object* v___x_1786_, lean_object* v___x_1787_, uint8_t v___x_1788_, uint8_t v___x_1789_, lean_object* v_ysx2_1790_, lean_object* v___t2_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___f_1801_; lean_object* v___x_1802_; 
v___x_1797_ = l_Lean_mkAppN(v___x_1772_, v_ysx1_1773_);
v___x_1798_ = lean_box(v___y_1783_);
v___x_1799_ = lean_box(v___x_1788_);
v___x_1800_ = lean_box(v___x_1789_);
lean_inc_ref(v_ysx2_1790_);
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1801_, 0, v___x_1774_);
lean_closure_set(v___f_1801_, 1, v_t1_1775_);
lean_closure_set(v___f_1801_, 2, v_val_1776_);
lean_closure_set(v___f_1801_, 3, v_P_1777_);
lean_closure_set(v___f_1801_, 4, v_xs1_1778_);
lean_closure_set(v___f_1801_, 5, v_xs2_1779_);
lean_closure_set(v___f_1801_, 6, v_indName_1780_);
lean_closure_set(v___f_1801_, 7, v___x_1781_);
lean_closure_set(v___f_1801_, 8, v___x_1782_);
lean_closure_set(v___f_1801_, 9, v_ysx2_1790_);
lean_closure_set(v___f_1801_, 10, v___x_1798_);
lean_closure_set(v___f_1801_, 11, v___x_1784_);
lean_closure_set(v___f_1801_, 12, v_tail_1785_);
lean_closure_set(v___f_1801_, 13, v___x_1786_);
lean_closure_set(v___f_1801_, 14, v___x_1797_);
lean_closure_set(v___f_1801_, 15, v___x_1787_);
lean_closure_set(v___f_1801_, 16, v_ysx1_1773_);
lean_closure_set(v___f_1801_, 17, v___x_1799_);
lean_closure_set(v___f_1801_, 18, v___x_1800_);
v___x_1802_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_ysx2_1790_, v___f_1801_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed(lean_object** _args){
lean_object* v___x_1803_ = _args[0];
lean_object* v_ysx1_1804_ = _args[1];
lean_object* v___x_1805_ = _args[2];
lean_object* v_t1_1806_ = _args[3];
lean_object* v_val_1807_ = _args[4];
lean_object* v_P_1808_ = _args[5];
lean_object* v_xs1_1809_ = _args[6];
lean_object* v_xs2_1810_ = _args[7];
lean_object* v_indName_1811_ = _args[8];
lean_object* v___x_1812_ = _args[9];
lean_object* v___x_1813_ = _args[10];
lean_object* v___y_1814_ = _args[11];
lean_object* v___x_1815_ = _args[12];
lean_object* v_tail_1816_ = _args[13];
lean_object* v___x_1817_ = _args[14];
lean_object* v___x_1818_ = _args[15];
lean_object* v___x_1819_ = _args[16];
lean_object* v___x_1820_ = _args[17];
lean_object* v_ysx2_1821_ = _args[18];
lean_object* v___t2_1822_ = _args[19];
lean_object* v___y_1823_ = _args[20];
lean_object* v___y_1824_ = _args[21];
lean_object* v___y_1825_ = _args[22];
lean_object* v___y_1826_ = _args[23];
lean_object* v___y_1827_ = _args[24];
_start:
{
uint8_t v___y_16912__boxed_1828_; uint8_t v___x_16917__boxed_1829_; uint8_t v___x_16918__boxed_1830_; lean_object* v_res_1831_; 
v___y_16912__boxed_1828_ = lean_unbox(v___y_1814_);
v___x_16917__boxed_1829_ = lean_unbox(v___x_1819_);
v___x_16918__boxed_1830_ = lean_unbox(v___x_1820_);
v_res_1831_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(v___x_1803_, v_ysx1_1804_, v___x_1805_, v_t1_1806_, v_val_1807_, v_P_1808_, v_xs1_1809_, v_xs2_1810_, v_indName_1811_, v___x_1812_, v___x_1813_, v___y_16912__boxed_1828_, v___x_1815_, v_tail_1816_, v___x_1817_, v___x_1818_, v___x_16917__boxed_1829_, v___x_16918__boxed_1830_, v_ysx2_1821_, v___t2_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v___t2_1822_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(lean_object* v___x_1832_, lean_object* v___x_1833_, lean_object* v_val_1834_, lean_object* v_P_1835_, lean_object* v_xs1_1836_, lean_object* v_xs2_1837_, lean_object* v_indName_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, uint8_t v___y_1841_, lean_object* v___x_1842_, lean_object* v_tail_1843_, lean_object* v___x_1844_, lean_object* v___x_1845_, uint8_t v___x_1846_, uint8_t v___x_1847_, lean_object* v_a_1848_, lean_object* v___x_1849_, lean_object* v_ysx1_1850_, lean_object* v_t1_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; 
v___x_1857_ = lean_box(v___y_1841_);
v___x_1858_ = lean_box(v___x_1846_);
v___x_1859_ = lean_box(v___x_1847_);
v___f_1860_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed), 25, 18);
lean_closure_set(v___f_1860_, 0, v___x_1832_);
lean_closure_set(v___f_1860_, 1, v_ysx1_1850_);
lean_closure_set(v___f_1860_, 2, v___x_1833_);
lean_closure_set(v___f_1860_, 3, v_t1_1851_);
lean_closure_set(v___f_1860_, 4, v_val_1834_);
lean_closure_set(v___f_1860_, 5, v_P_1835_);
lean_closure_set(v___f_1860_, 6, v_xs1_1836_);
lean_closure_set(v___f_1860_, 7, v_xs2_1837_);
lean_closure_set(v___f_1860_, 8, v_indName_1838_);
lean_closure_set(v___f_1860_, 9, v___x_1839_);
lean_closure_set(v___f_1860_, 10, v___x_1840_);
lean_closure_set(v___f_1860_, 11, v___x_1857_);
lean_closure_set(v___f_1860_, 12, v___x_1842_);
lean_closure_set(v___f_1860_, 13, v_tail_1843_);
lean_closure_set(v___f_1860_, 14, v___x_1844_);
lean_closure_set(v___f_1860_, 15, v___x_1845_);
lean_closure_set(v___f_1860_, 16, v___x_1858_);
lean_closure_set(v___f_1860_, 17, v___x_1859_);
v___x_1861_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1848_, v___x_1849_, v___f_1860_, v___x_1846_, v___x_1846_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed(lean_object** _args){
lean_object* v___x_1862_ = _args[0];
lean_object* v___x_1863_ = _args[1];
lean_object* v_val_1864_ = _args[2];
lean_object* v_P_1865_ = _args[3];
lean_object* v_xs1_1866_ = _args[4];
lean_object* v_xs2_1867_ = _args[5];
lean_object* v_indName_1868_ = _args[6];
lean_object* v___x_1869_ = _args[7];
lean_object* v___x_1870_ = _args[8];
lean_object* v___y_1871_ = _args[9];
lean_object* v___x_1872_ = _args[10];
lean_object* v_tail_1873_ = _args[11];
lean_object* v___x_1874_ = _args[12];
lean_object* v___x_1875_ = _args[13];
lean_object* v___x_1876_ = _args[14];
lean_object* v___x_1877_ = _args[15];
lean_object* v_a_1878_ = _args[16];
lean_object* v___x_1879_ = _args[17];
lean_object* v_ysx1_1880_ = _args[18];
lean_object* v_t1_1881_ = _args[19];
lean_object* v___y_1882_ = _args[20];
lean_object* v___y_1883_ = _args[21];
lean_object* v___y_1884_ = _args[22];
lean_object* v___y_1885_ = _args[23];
lean_object* v___y_1886_ = _args[24];
_start:
{
uint8_t v___y_16975__boxed_1887_; uint8_t v___x_16980__boxed_1888_; uint8_t v___x_16981__boxed_1889_; lean_object* v_res_1890_; 
v___y_16975__boxed_1887_ = lean_unbox(v___y_1871_);
v___x_16980__boxed_1888_ = lean_unbox(v___x_1876_);
v___x_16981__boxed_1889_ = lean_unbox(v___x_1877_);
v_res_1890_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(v___x_1862_, v___x_1863_, v_val_1864_, v_P_1865_, v_xs1_1866_, v_xs2_1867_, v_indName_1868_, v___x_1869_, v___x_1870_, v___y_16975__boxed_1887_, v___x_1872_, v_tail_1873_, v___x_1874_, v___x_1875_, v___x_16980__boxed_1888_, v___x_16981__boxed_1889_, v_a_1878_, v___x_1879_, v_ysx1_1880_, v_t1_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(lean_object* v_t1_1891_, lean_object* v___f_1892_, lean_object* v___x_1893_, lean_object* v_t2_1894_, lean_object* v_numIndices_1895_, lean_object* v___x_1896_, lean_object* v_val_1897_, lean_object* v_P_1898_, lean_object* v_xs1_1899_, lean_object* v_xs2_1900_, lean_object* v_indName_1901_, lean_object* v___x_1902_, uint8_t v___y_1903_, lean_object* v___x_1904_, lean_object* v_tail_1905_, lean_object* v___x_1906_, uint8_t v___x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
lean_inc_ref(v_t1_1891_);
v___x_1913_ = l_Lean_Meta_whnfD(v_t1_1891_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Expr_bindingDomain_x21(v_a_1914_);
lean_dec(v_a_1914_);
v___x_1916_ = 0;
lean_inc_ref(v___f_1892_);
v___x_1917_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1915_, v___f_1892_, v___x_1916_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc_n(v_a_1918_, 2);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_mk_empty_array_with_capacity(v___x_1919_);
lean_inc_ref(v___x_1920_);
v___x_1921_ = lean_array_push(v___x_1920_, v_a_1918_);
v___x_1922_ = l_Lean_Meta_instantiateForall(v_t1_1891_, v___x_1921_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
lean_dec_ref(v___x_1921_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1924_ = l_Lean_Expr_app___override(v___x_1893_, v_a_1918_);
lean_inc_ref(v_t2_1894_);
v___x_1925_ = l_Lean_Meta_whnfD(v_t2_1894_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_Expr_bindingDomain_x21(v_a_1926_);
lean_dec(v_a_1926_);
v___x_1928_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1927_, v___f_1892_, v___x_1916_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
lean_inc_ref(v___x_1920_);
v___x_1930_ = lean_array_push(v___x_1920_, v_a_1929_);
v___x_1931_ = l_Lean_Meta_instantiateForall(v_t2_1894_, v___x_1930_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1945_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1945_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_nat_add(v_numIndices_1895_, v___x_1919_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set_tag(v___x_1934_, 1);
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1938_ = v___x_1934_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___f_1942_; lean_object* v___x_1943_; 
v___x_1939_ = lean_box(v___y_1903_);
v___x_1940_ = lean_box(v___x_1916_);
v___x_1941_ = lean_box(v___x_1907_);
lean_inc_ref(v___x_1938_);
v___f_1942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1942_, 0, v___x_1924_);
lean_closure_set(v___f_1942_, 1, v___x_1896_);
lean_closure_set(v___f_1942_, 2, v_val_1897_);
lean_closure_set(v___f_1942_, 3, v_P_1898_);
lean_closure_set(v___f_1942_, 4, v_xs1_1899_);
lean_closure_set(v___f_1942_, 5, v_xs2_1900_);
lean_closure_set(v___f_1942_, 6, v_indName_1901_);
lean_closure_set(v___f_1942_, 7, v___x_1902_);
lean_closure_set(v___f_1942_, 8, v___x_1930_);
lean_closure_set(v___f_1942_, 9, v___x_1939_);
lean_closure_set(v___f_1942_, 10, v___x_1904_);
lean_closure_set(v___f_1942_, 11, v_tail_1905_);
lean_closure_set(v___f_1942_, 12, v___x_1906_);
lean_closure_set(v___f_1942_, 13, v___x_1920_);
lean_closure_set(v___f_1942_, 14, v___x_1940_);
lean_closure_set(v___f_1942_, 15, v___x_1941_);
lean_closure_set(v___f_1942_, 16, v_a_1932_);
lean_closure_set(v___f_1942_, 17, v___x_1938_);
v___x_1943_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1923_, v___x_1938_, v___f_1942_, v___x_1916_, v___x_1916_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1943_;
}
}
}
else
{
lean_dec_ref(v___x_1930_);
lean_dec_ref(v___x_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v___x_1920_);
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
return v___x_1931_;
}
}
else
{
lean_dec_ref(v___x_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v___x_1920_);
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_t2_1894_);
return v___x_1928_;
}
}
else
{
lean_dec_ref(v___x_1924_);
lean_dec(v_a_1923_);
lean_dec_ref(v___x_1920_);
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_t2_1894_);
lean_dec_ref(v___f_1892_);
return v___x_1925_;
}
}
else
{
lean_dec_ref(v___x_1920_);
lean_dec(v_a_1918_);
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_t2_1894_);
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___f_1892_);
return v___x_1922_;
}
}
else
{
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_t2_1894_);
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___f_1892_);
lean_dec_ref(v_t1_1891_);
return v___x_1917_;
}
}
else
{
lean_dec_ref(v___x_1906_);
lean_dec(v_tail_1905_);
lean_dec_ref(v___x_1904_);
lean_dec(v___x_1902_);
lean_dec(v_indName_1901_);
lean_dec_ref(v_xs2_1900_);
lean_dec_ref(v_xs1_1899_);
lean_dec_ref(v_P_1898_);
lean_dec_ref(v_val_1897_);
lean_dec(v___x_1896_);
lean_dec_ref(v_t2_1894_);
lean_dec_ref(v___x_1893_);
lean_dec_ref(v___f_1892_);
lean_dec_ref(v_t1_1891_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed(lean_object** _args){
lean_object* v_t1_1946_ = _args[0];
lean_object* v___f_1947_ = _args[1];
lean_object* v___x_1948_ = _args[2];
lean_object* v_t2_1949_ = _args[3];
lean_object* v_numIndices_1950_ = _args[4];
lean_object* v___x_1951_ = _args[5];
lean_object* v_val_1952_ = _args[6];
lean_object* v_P_1953_ = _args[7];
lean_object* v_xs1_1954_ = _args[8];
lean_object* v_xs2_1955_ = _args[9];
lean_object* v_indName_1956_ = _args[10];
lean_object* v___x_1957_ = _args[11];
lean_object* v___y_1958_ = _args[12];
lean_object* v___x_1959_ = _args[13];
lean_object* v_tail_1960_ = _args[14];
lean_object* v___x_1961_ = _args[15];
lean_object* v___x_1962_ = _args[16];
lean_object* v___y_1963_ = _args[17];
lean_object* v___y_1964_ = _args[18];
lean_object* v___y_1965_ = _args[19];
lean_object* v___y_1966_ = _args[20];
lean_object* v___y_1967_ = _args[21];
_start:
{
uint8_t v___y_17042__boxed_1968_; uint8_t v___x_17046__boxed_1969_; lean_object* v_res_1970_; 
v___y_17042__boxed_1968_ = lean_unbox(v___y_1958_);
v___x_17046__boxed_1969_ = lean_unbox(v___x_1962_);
v_res_1970_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(v_t1_1946_, v___f_1947_, v___x_1948_, v_t2_1949_, v_numIndices_1950_, v___x_1951_, v_val_1952_, v_P_1953_, v_xs1_1954_, v_xs2_1955_, v_indName_1956_, v___x_1957_, v___y_17042__boxed_1968_, v___x_1959_, v_tail_1960_, v___x_1961_, v___x_17046__boxed_1969_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v_numIndices_1950_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(lean_object* v___x_1971_, lean_object* v_xs1_1972_, lean_object* v_t1_1973_, lean_object* v___f_1974_, lean_object* v_numIndices_1975_, lean_object* v___x_1976_, lean_object* v_val_1977_, lean_object* v_P_1978_, lean_object* v_indName_1979_, lean_object* v___x_1980_, uint8_t v___y_1981_, lean_object* v_tail_1982_, lean_object* v___x_1983_, uint8_t v___x_1984_, lean_object* v_xs2_1985_, lean_object* v_t2_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v___x_1971_);
v___x_1992_ = l_Lean_mkAppN(v___x_1971_, v_xs1_1972_);
v___x_1993_ = lean_box(v___y_1981_);
v___x_1994_ = lean_box(v___x_1984_);
lean_inc_ref(v_xs2_1985_);
v___f_1995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed), 22, 17);
lean_closure_set(v___f_1995_, 0, v_t1_1973_);
lean_closure_set(v___f_1995_, 1, v___f_1974_);
lean_closure_set(v___f_1995_, 2, v___x_1992_);
lean_closure_set(v___f_1995_, 3, v_t2_1986_);
lean_closure_set(v___f_1995_, 4, v_numIndices_1975_);
lean_closure_set(v___f_1995_, 5, v___x_1976_);
lean_closure_set(v___f_1995_, 6, v_val_1977_);
lean_closure_set(v___f_1995_, 7, v_P_1978_);
lean_closure_set(v___f_1995_, 8, v_xs1_1972_);
lean_closure_set(v___f_1995_, 9, v_xs2_1985_);
lean_closure_set(v___f_1995_, 10, v_indName_1979_);
lean_closure_set(v___f_1995_, 11, v___x_1980_);
lean_closure_set(v___f_1995_, 12, v___x_1993_);
lean_closure_set(v___f_1995_, 13, v___x_1971_);
lean_closure_set(v___f_1995_, 14, v_tail_1982_);
lean_closure_set(v___f_1995_, 15, v___x_1983_);
lean_closure_set(v___f_1995_, 16, v___x_1994_);
v___x_1996_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs2_1985_, v___f_1995_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed(lean_object** _args){
lean_object* v___x_1997_ = _args[0];
lean_object* v_xs1_1998_ = _args[1];
lean_object* v_t1_1999_ = _args[2];
lean_object* v___f_2000_ = _args[3];
lean_object* v_numIndices_2001_ = _args[4];
lean_object* v___x_2002_ = _args[5];
lean_object* v_val_2003_ = _args[6];
lean_object* v_P_2004_ = _args[7];
lean_object* v_indName_2005_ = _args[8];
lean_object* v___x_2006_ = _args[9];
lean_object* v___y_2007_ = _args[10];
lean_object* v_tail_2008_ = _args[11];
lean_object* v___x_2009_ = _args[12];
lean_object* v___x_2010_ = _args[13];
lean_object* v_xs2_2011_ = _args[14];
lean_object* v_t2_2012_ = _args[15];
lean_object* v___y_2013_ = _args[16];
lean_object* v___y_2014_ = _args[17];
lean_object* v___y_2015_ = _args[18];
lean_object* v___y_2016_ = _args[19];
lean_object* v___y_2017_ = _args[20];
_start:
{
uint8_t v___y_17159__boxed_2018_; uint8_t v___x_17162__boxed_2019_; lean_object* v_res_2020_; 
v___y_17159__boxed_2018_ = lean_unbox(v___y_2007_);
v___x_17162__boxed_2019_ = lean_unbox(v___x_2010_);
v_res_2020_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(v___x_1997_, v_xs1_1998_, v_t1_1999_, v___f_2000_, v_numIndices_2001_, v___x_2002_, v_val_2003_, v_P_2004_, v_indName_2005_, v___x_2006_, v___y_17159__boxed_2018_, v_tail_2008_, v___x_2009_, v___x_17162__boxed_2019_, v_xs2_2011_, v_t2_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(lean_object* v___x_2021_, lean_object* v___f_2022_, lean_object* v_numIndices_2023_, lean_object* v___x_2024_, lean_object* v_val_2025_, lean_object* v_P_2026_, lean_object* v_indName_2027_, lean_object* v___x_2028_, uint8_t v___y_2029_, lean_object* v_tail_2030_, lean_object* v___x_2031_, uint8_t v___x_2032_, lean_object* v_a_2033_, lean_object* v___x_2034_, lean_object* v_xs1_2035_, lean_object* v_t1_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___f_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2042_ = lean_box(v___y_2029_);
v___x_2043_ = lean_box(v___x_2032_);
v___f_2044_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed), 21, 14);
lean_closure_set(v___f_2044_, 0, v___x_2021_);
lean_closure_set(v___f_2044_, 1, v_xs1_2035_);
lean_closure_set(v___f_2044_, 2, v_t1_2036_);
lean_closure_set(v___f_2044_, 3, v___f_2022_);
lean_closure_set(v___f_2044_, 4, v_numIndices_2023_);
lean_closure_set(v___f_2044_, 5, v___x_2024_);
lean_closure_set(v___f_2044_, 6, v_val_2025_);
lean_closure_set(v___f_2044_, 7, v_P_2026_);
lean_closure_set(v___f_2044_, 8, v_indName_2027_);
lean_closure_set(v___f_2044_, 9, v___x_2028_);
lean_closure_set(v___f_2044_, 10, v___x_2042_);
lean_closure_set(v___f_2044_, 11, v_tail_2030_);
lean_closure_set(v___f_2044_, 12, v___x_2031_);
lean_closure_set(v___f_2044_, 13, v___x_2043_);
v___x_2045_ = 0;
v___x_2046_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2033_, v___x_2034_, v___f_2044_, v___x_2045_, v___x_2045_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed(lean_object** _args){
lean_object* v___x_2047_ = _args[0];
lean_object* v___f_2048_ = _args[1];
lean_object* v_numIndices_2049_ = _args[2];
lean_object* v___x_2050_ = _args[3];
lean_object* v_val_2051_ = _args[4];
lean_object* v_P_2052_ = _args[5];
lean_object* v_indName_2053_ = _args[6];
lean_object* v___x_2054_ = _args[7];
lean_object* v___y_2055_ = _args[8];
lean_object* v_tail_2056_ = _args[9];
lean_object* v___x_2057_ = _args[10];
lean_object* v___x_2058_ = _args[11];
lean_object* v_a_2059_ = _args[12];
lean_object* v___x_2060_ = _args[13];
lean_object* v_xs1_2061_ = _args[14];
lean_object* v_t1_2062_ = _args[15];
lean_object* v___y_2063_ = _args[16];
lean_object* v___y_2064_ = _args[17];
lean_object* v___y_2065_ = _args[18];
lean_object* v___y_2066_ = _args[19];
lean_object* v___y_2067_ = _args[20];
_start:
{
uint8_t v___y_17211__boxed_2068_; uint8_t v___x_17214__boxed_2069_; lean_object* v_res_2070_; 
v___y_17211__boxed_2068_ = lean_unbox(v___y_2055_);
v___x_17214__boxed_2069_ = lean_unbox(v___x_2058_);
v_res_2070_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(v___x_2047_, v___f_2048_, v_numIndices_2049_, v___x_2050_, v_val_2051_, v_P_2052_, v_indName_2053_, v___x_2054_, v___y_17211__boxed_2068_, v_tail_2056_, v___x_2057_, v___x_17214__boxed_2069_, v_a_2059_, v___x_2060_, v_xs1_2061_, v_t1_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(lean_object* v_val_2071_, lean_object* v___x_2072_, lean_object* v___f_2073_, lean_object* v___x_2074_, lean_object* v_indName_2075_, lean_object* v___x_2076_, uint8_t v___y_2077_, lean_object* v_tail_2078_, lean_object* v___x_2079_, uint8_t v___x_2080_, lean_object* v_a_2081_, lean_object* v_P_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_numParams_2088_; lean_object* v_numIndices_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___f_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; 
v_numParams_2088_ = lean_ctor_get(v_val_2071_, 1);
v_numIndices_2089_ = lean_ctor_get(v_val_2071_, 2);
lean_inc(v_numIndices_2089_);
lean_inc(v_numParams_2088_);
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_numParams_2088_);
v___x_2091_ = lean_box(v___y_2077_);
v___x_2092_ = lean_box(v___x_2080_);
lean_inc_ref(v___x_2090_);
lean_inc_ref(v_a_2081_);
v___f_2093_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed), 21, 14);
lean_closure_set(v___f_2093_, 0, v___x_2072_);
lean_closure_set(v___f_2093_, 1, v___f_2073_);
lean_closure_set(v___f_2093_, 2, v_numIndices_2089_);
lean_closure_set(v___f_2093_, 3, v___x_2074_);
lean_closure_set(v___f_2093_, 4, v_val_2071_);
lean_closure_set(v___f_2093_, 5, v_P_2082_);
lean_closure_set(v___f_2093_, 6, v_indName_2075_);
lean_closure_set(v___f_2093_, 7, v___x_2076_);
lean_closure_set(v___f_2093_, 8, v___x_2091_);
lean_closure_set(v___f_2093_, 9, v_tail_2078_);
lean_closure_set(v___f_2093_, 10, v___x_2079_);
lean_closure_set(v___f_2093_, 11, v___x_2092_);
lean_closure_set(v___f_2093_, 12, v_a_2081_);
lean_closure_set(v___f_2093_, 13, v___x_2090_);
v___x_2094_ = 0;
v___x_2095_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2081_, v___x_2090_, v___f_2093_, v___x_2094_, v___x_2094_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed(lean_object** _args){
lean_object* v_val_2096_ = _args[0];
lean_object* v___x_2097_ = _args[1];
lean_object* v___f_2098_ = _args[2];
lean_object* v___x_2099_ = _args[3];
lean_object* v_indName_2100_ = _args[4];
lean_object* v___x_2101_ = _args[5];
lean_object* v___y_2102_ = _args[6];
lean_object* v_tail_2103_ = _args[7];
lean_object* v___x_2104_ = _args[8];
lean_object* v___x_2105_ = _args[9];
lean_object* v_a_2106_ = _args[10];
lean_object* v_P_2107_ = _args[11];
lean_object* v___y_2108_ = _args[12];
lean_object* v___y_2109_ = _args[13];
lean_object* v___y_2110_ = _args[14];
lean_object* v___y_2111_ = _args[15];
lean_object* v___y_2112_ = _args[16];
_start:
{
uint8_t v___y_17269__boxed_2113_; uint8_t v___x_17272__boxed_2114_; lean_object* v_res_2115_; 
v___y_17269__boxed_2113_ = lean_unbox(v___y_2102_);
v___x_17272__boxed_2114_ = lean_unbox(v___x_2105_);
v_res_2115_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(v_val_2096_, v___x_2097_, v___f_2098_, v___x_2099_, v_indName_2100_, v___x_2101_, v___y_17269__boxed_2113_, v_tail_2103_, v___x_2104_, v___x_17272__boxed_2114_, v_a_2106_, v_P_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2115_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0);
v___x_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2122_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
lean_ctor_set(v___x_2122_, 2, v___x_2121_);
lean_ctor_set(v___x_2122_, 3, v___x_2121_);
lean_ctor_set(v___x_2122_, 4, v___x_2121_);
lean_ctor_set(v___x_2122_, 5, v___x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(lean_object* v_declName_2123_, uint8_t v_s_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v_env_2129_; lean_object* v_nextMacroScope_2130_; lean_object* v_ngen_2131_; lean_object* v_auxDeclNGen_2132_; lean_object* v_traceState_2133_; lean_object* v_messages_2134_; lean_object* v_infoState_2135_; lean_object* v_snapshotTasks_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2165_; 
v___x_2128_ = lean_st_ref_take(v___y_2126_);
v_env_2129_ = lean_ctor_get(v___x_2128_, 0);
v_nextMacroScope_2130_ = lean_ctor_get(v___x_2128_, 1);
v_ngen_2131_ = lean_ctor_get(v___x_2128_, 2);
v_auxDeclNGen_2132_ = lean_ctor_get(v___x_2128_, 3);
v_traceState_2133_ = lean_ctor_get(v___x_2128_, 4);
v_messages_2134_ = lean_ctor_get(v___x_2128_, 6);
v_infoState_2135_ = lean_ctor_get(v___x_2128_, 7);
v_snapshotTasks_2136_ = lean_ctor_get(v___x_2128_, 8);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v___x_2128_, 5);
lean_dec(v_unused_2166_);
v___x_2138_ = v___x_2128_;
v_isShared_2139_ = v_isSharedCheck_2165_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_snapshotTasks_2136_);
lean_inc(v_infoState_2135_);
lean_inc(v_messages_2134_);
lean_inc(v_traceState_2133_);
lean_inc(v_auxDeclNGen_2132_);
lean_inc(v_ngen_2131_);
lean_inc(v_nextMacroScope_2130_);
lean_inc(v_env_2129_);
lean_dec(v___x_2128_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2165_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
uint8_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2140_ = 0;
v___x_2141_ = lean_box(0);
v___x_2142_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2129_, v_declName_2123_, v_s_2124_, v___x_2140_, v___x_2141_);
v___x_2143_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 5, v___x_2143_);
lean_ctor_set(v___x_2138_, 0, v___x_2142_);
v___x_2145_ = v___x_2138_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_nextMacroScope_2130_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_ngen_2131_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_auxDeclNGen_2132_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_traceState_2133_);
lean_ctor_set(v_reuseFailAlloc_2164_, 5, v___x_2143_);
lean_ctor_set(v_reuseFailAlloc_2164_, 6, v_messages_2134_);
lean_ctor_set(v_reuseFailAlloc_2164_, 7, v_infoState_2135_);
lean_ctor_set(v_reuseFailAlloc_2164_, 8, v_snapshotTasks_2136_);
v___x_2145_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_mctx_2148_; lean_object* v_zetaDeltaFVarIds_2149_; lean_object* v_postponed_2150_; lean_object* v_diag_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2162_; 
v___x_2146_ = lean_st_ref_put(v___y_2126_, v___x_2145_);
v___x_2147_ = lean_st_ref_take(v___y_2125_);
v_mctx_2148_ = lean_ctor_get(v___x_2147_, 0);
v_zetaDeltaFVarIds_2149_ = lean_ctor_get(v___x_2147_, 2);
v_postponed_2150_ = lean_ctor_get(v___x_2147_, 3);
v_diag_2151_ = lean_ctor_get(v___x_2147_, 4);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v___x_2147_, 1);
lean_dec(v_unused_2163_);
v___x_2153_ = v___x_2147_;
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_diag_2151_);
lean_inc(v_postponed_2150_);
lean_inc(v_zetaDeltaFVarIds_2149_);
lean_inc(v_mctx_2148_);
lean_dec(v___x_2147_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2162_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2156_);
v___x_2158_ = v___x_2153_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_mctx_2148_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2161_, 2, v_zetaDeltaFVarIds_2149_);
lean_ctor_set(v_reuseFailAlloc_2161_, 3, v_postponed_2150_);
lean_ctor_set(v_reuseFailAlloc_2161_, 4, v_diag_2151_);
v___x_2158_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_st_ref_put(v___y_2125_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2155_);
return v___x_2160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___boxed(lean_object* v_declName_2167_, lean_object* v_s_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_s_boxed_2172_; lean_object* v_res_2173_; 
v_s_boxed_2172_ = lean_unbox(v_s_2168_);
v_res_2173_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2167_, v_s_boxed_2172_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec(v___y_2169_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(lean_object* v_declName_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
uint8_t v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = 0;
v___x_2181_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2174_, v___x_2180_, v___y_2176_, v___y_2178_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7___boxed(lean_object* v_declName_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
if (lean_obj_tag(v_a_2189_) == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = l_List_reverse___redArg(v_a_2190_);
return v___x_2191_;
}
else
{
lean_object* v_head_2192_; lean_object* v_tail_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2202_; 
v_head_2192_ = lean_ctor_get(v_a_2189_, 0);
v_tail_2193_ = lean_ctor_get(v_a_2189_, 1);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_a_2189_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2195_ = v_a_2189_;
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_tail_2193_);
lean_inc(v_head_2192_);
lean_dec(v_a_2189_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = l_Lean_mkLevelParam(v_head_2192_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 1, v_a_2190_);
lean_ctor_set(v___x_2195_, 0, v___x_2197_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_a_2190_);
v___x_2199_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
v_a_2189_ = v_tail_2193_;
v_a_2190_ = v___x_2199_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
lean_ctor_set(v___x_2207_, 2, v___x_2206_);
lean_ctor_set(v___x_2207_, 3, v___x_2206_);
lean_ctor_set(v___x_2207_, 4, v___x_2205_);
lean_ctor_set(v___x_2207_, 5, v___x_2205_);
lean_ctor_set(v___x_2207_, 6, v___x_2205_);
lean_ctor_set(v___x_2207_, 7, v___x_2205_);
lean_ctor_set(v___x_2207_, 8, v___x_2205_);
lean_ctor_set(v___x_2207_, 9, v___x_2205_);
lean_ctor_set(v___x_2207_, 10, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_unsigned_to_nat(32u);
v___x_2209_ = lean_mk_empty_array_with_capacity(v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2211_ = ((size_t)5ULL);
v___x_2212_ = lean_unsigned_to_nat(0u);
v___x_2213_ = lean_unsigned_to_nat(32u);
v___x_2214_ = lean_mk_empty_array_with_capacity(v___x_2213_);
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_2216_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2212_);
lean_ctor_set(v___x_2216_, 3, v___x_2212_);
lean_ctor_set_usize(v___x_2216_, 4, v___x_2211_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2217_ = lean_box(1);
v___x_2218_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_2219_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_2218_);
lean_ctor_set(v___x_2220_, 2, v___x_2217_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_2226_ = l_Lean_stringToMessageData(v___x_2225_);
return v___x_2226_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_2229_ = l_Lean_stringToMessageData(v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2231_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_2232_ = l_Lean_stringToMessageData(v___x_2231_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_2241_ = l_Lean_stringToMessageData(v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_2242_, lean_object* v_declHint_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_env_2248_; uint8_t v___x_2249_; 
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_st_ref_get(v___y_2244_);
v_env_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_env_2248_);
lean_dec(v___x_2247_);
v___x_2249_ = l_Lean_Name_isAnonymous(v_declHint_2243_);
if (v___x_2249_ == 0)
{
uint8_t v_isExporting_2250_; 
v_isExporting_2250_ = lean_ctor_get_uint8(v_env_2248_, sizeof(void*)*8);
if (v_isExporting_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec_ref(v_env_2248_);
lean_dec(v_declHint_2243_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_msg_2242_);
return v___x_2251_;
}
else
{
lean_object* v___x_2252_; uint8_t v___x_2253_; 
lean_inc_ref(v_env_2248_);
v___x_2252_ = l_Lean_Environment_setExporting(v_env_2248_, v___x_2249_);
lean_inc(v_declHint_2243_);
lean_inc_ref(v___x_2252_);
v___x_2253_ = l_Lean_Environment_contains(v___x_2252_, v_declHint_2243_, v_isExporting_2250_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; 
lean_dec_ref(v___x_2252_);
lean_dec_ref(v_env_2248_);
lean_dec(v_declHint_2243_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_msg_2242_);
return v___x_2254_;
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v_c_2260_; lean_object* v___x_2261_; 
v___x_2255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_2256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_2257_ = l_Lean_Options_empty;
v___x_2258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2252_);
lean_ctor_set(v___x_2258_, 1, v___x_2255_);
lean_ctor_set(v___x_2258_, 2, v___x_2256_);
lean_ctor_set(v___x_2258_, 3, v___x_2257_);
lean_inc(v_declHint_2243_);
v___x_2259_ = l_Lean_MessageData_ofConstName(v_declHint_2243_, v___x_2249_);
v_c_2260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2260_, 0, v___x_2258_);
lean_ctor_set(v_c_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2248_, v_declHint_2243_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v_env_2248_);
lean_dec(v_declHint_2243_);
v___x_2262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_c_2260_);
v___x_2264_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2263_);
lean_ctor_set(v___x_2265_, 1, v___x_2264_);
v___x_2266_ = l_Lean_MessageData_note(v___x_2265_);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v_msg_2242_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2303_; 
v_val_2269_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2271_ = v___x_2261_;
v_isShared_2272_ = v_isSharedCheck_2303_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_val_2269_);
lean_dec(v___x_2261_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2303_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v_mod_2275_; uint8_t v___x_2276_; 
v___x_2273_ = l_Lean_Environment_header(v_env_2248_);
lean_dec_ref(v_env_2248_);
v___x_2274_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2273_);
v_mod_2275_ = lean_array_get(v___x_2246_, v___x_2274_, v_val_2269_);
lean_dec(v_val_2269_);
lean_dec_ref(v___x_2274_);
v___x_2276_ = l_Lean_isPrivateName(v_declHint_2243_);
lean_dec(v_declHint_2243_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_c_2260_);
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_MessageData_ofName(v_mod_2275_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = l_Lean_MessageData_note(v___x_2284_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v_msg_2242_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2286_);
v___x_2288_ = v___x_2271_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2290_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v_c_2260_);
v___x_2292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_MessageData_ofName(v_mod_2275_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
v___x_2296_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_2297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2295_);
lean_ctor_set(v___x_2297_, 1, v___x_2296_);
v___x_2298_ = l_Lean_MessageData_note(v___x_2297_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_msg_2242_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set_tag(v___x_2271_, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2299_);
v___x_2301_ = v___x_2271_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2304_; 
lean_dec_ref(v_env_2248_);
lean_dec(v_declHint_2243_);
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_msg_2242_);
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_2305_, lean_object* v_declHint_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2305_, v_declHint_2306_, v___y_2307_);
lean_dec(v___y_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_2310_, lean_object* v_declHint_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2327_; 
v___x_2317_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2310_, v_declHint_2311_, v___y_2315_);
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2320_ = v___x_2317_;
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2327_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2322_ = l_Lean_unknownIdentifierMessageTag;
v___x_2323_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v_a_2318_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_2328_, lean_object* v_declHint_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2328_, v_declHint_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_toCold_2343_; lean_object* v_currRecDepth_2344_; lean_object* v_ref_2345_; uint8_t v_diag_2346_; uint8_t v_suppressElabErrors_2347_; lean_object* v_ref_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_toCold_2343_ = lean_ctor_get(v___y_2340_, 0);
v_currRecDepth_2344_ = lean_ctor_get(v___y_2340_, 1);
v_ref_2345_ = lean_ctor_get(v___y_2340_, 2);
v_diag_2346_ = lean_ctor_get_uint8(v___y_2340_, sizeof(void*)*3);
v_suppressElabErrors_2347_ = lean_ctor_get_uint8(v___y_2340_, sizeof(void*)*3 + 1);
v_ref_2348_ = l_Lean_replaceRef(v_ref_2336_, v_ref_2345_);
lean_inc(v_currRecDepth_2344_);
lean_inc_ref(v_toCold_2343_);
v___x_2349_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2349_, 0, v_toCold_2343_);
lean_ctor_set(v___x_2349_, 1, v_currRecDepth_2344_);
lean_ctor_set(v___x_2349_, 2, v_ref_2348_);
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*3, v_diag_2346_);
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*3 + 1, v_suppressElabErrors_2347_);
v___x_2350_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_2337_, v___y_2338_, v___y_2339_, v___x_2349_, v___y_2341_);
lean_dec_ref_known(v___x_2349_, 3);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_2351_, lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2351_, v_msg_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v_ref_2351_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_2359_, lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; lean_object* v_a_2368_; lean_object* v___x_2369_; 
v___x_2367_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2360_, v_declHint_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2359_, v_a_2368_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_2370_, lean_object* v_msg_2371_, lean_object* v_declHint_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2370_, v_msg_2371_, v_declHint_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v_ref_2370_);
return v_res_2378_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2382_, lean_object* v_constName_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2389_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2390_ = 0;
lean_inc(v_constName_2383_);
v___x_2391_ = l_Lean_MessageData_ofConstName(v_constName_2383_, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2389_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2382_, v___x_2394_, v_constName_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2396_, lean_object* v_constName_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2396_, v_constName_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_ref_2410_; lean_object* v___x_2411_; 
v_ref_2410_ = lean_ctor_get(v___y_2407_, 2);
v___x_2411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2410_, v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(lean_object* v_constName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v_env_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_st_ref_get(v___y_2423_);
v_env_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc_ref(v_env_2426_);
lean_dec(v___x_2425_);
v___x_2427_ = 0;
lean_inc(v_constName_2419_);
v___x_2428_ = l_Lean_Environment_findConstVal_x3f(v_env_2426_, v_constName_2419_, v___x_2427_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2429_;
}
else
{
lean_object* v_val_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_constName_2419_);
v_val_2430_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2428_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_val_2430_);
lean_dec(v___x_2428_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 0);
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_val_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1___boxed(lean_object* v_constName_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v_constName_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v_env_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = lean_st_ref_get(v___y_2449_);
v_env_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc_ref(v_env_2452_);
lean_dec(v___x_2451_);
v___x_2453_ = 0;
lean_inc(v_constName_2445_);
v___x_2454_ = l_Lean_Environment_find_x3f(v_env_2452_, v_constName_2445_, v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2455_;
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_constName_2445_);
v_val_2456_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_val_2456_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_val_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0___boxed(lean_object* v_constName_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_constName_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4));
v___x_2478_ = lean_unsigned_to_nat(58u);
v___x_2479_ = lean_unsigned_to_nat(81u);
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2481_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2482_ = l_mkPanicMessageWithDecl(v___x_2481_, v___x_2480_, v___x_2479_, v___x_2478_, v___x_2477_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2483_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_2484_ = lean_unsigned_to_nat(60u);
v___x_2485_ = lean_unsigned_to_nat(74u);
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2488_ = l_mkPanicMessageWithDecl(v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_, v___x_2483_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(lean_object* v_indName_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_declName_2495_; lean_object* v___x_2496_; 
lean_inc_n(v_indName_2489_, 2);
v_declName_2495_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(v_indName_2489_);
v___x_2496_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_indName_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
if (lean_obj_tag(v_a_2497_) == 5)
{
lean_object* v_toCold_2498_; lean_object* v_val_2499_; lean_object* v_options_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v_a_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___y_2508_; uint8_t v___x_2654_; 
v_toCold_2498_ = lean_ctor_get(v_a_2492_, 0);
v_val_2499_ = lean_ctor_get(v_a_2497_, 0);
lean_inc_ref(v_val_2499_);
lean_dec_ref_known(v_a_2497_, 1);
v_options_2500_ = lean_ctor_get(v_toCold_2498_, 2);
lean_inc(v_indName_2489_);
v___x_2501_ = l_Lean_mkCtorElimName(v_indName_2489_);
v___x_2502_ = 1;
v___x_2503_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_2501_, v___x_2502_, v_a_2493_);
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(2u);
v___x_2506_ = l_Lean_InductiveVal_numCtors(v_val_2499_);
v___x_2654_ = lean_nat_dec_lt(v___x_2505_, v___x_2506_);
if (v___x_2654_ == 0)
{
lean_dec(v_a_2504_);
v___y_2508_ = v___x_2654_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
v___x_2656_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_2500_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_dec(v_a_2504_);
v___y_2508_ = v___x_2656_;
goto v___jp_2507_;
}
else
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_unbox(v_a_2504_);
lean_dec(v_a_2504_);
v___y_2508_ = v___x_2657_;
goto v___jp_2507_;
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_inc(v_indName_2489_);
v___x_2509_ = l_Lean_mkCasesOnName(v_indName_2489_);
lean_inc(v___x_2509_);
v___x_2510_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v___x_2509_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v_levelParams_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref_known(v___x_2510_, 1);
v_levelParams_2512_ = lean_ctor_get(v_a_2511_, 1);
lean_inc_n(v_levelParams_2512_, 2);
lean_dec(v_a_2511_);
v___x_2513_ = lean_box(0);
v___x_2514_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_2512_, v___x_2513_);
if (lean_obj_tag(v___x_2514_) == 1)
{
lean_object* v_head_2515_; lean_object* v_tail_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2643_; 
v_head_2515_ = lean_ctor_get(v___x_2514_, 0);
v_tail_2516_ = lean_ctor_get(v___x_2514_, 1);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2518_ = v___x_2514_;
v_isShared_2519_ = v_isSharedCheck_2643_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_tail_2516_);
lean_inc(v_head_2515_);
lean_dec(v___x_2514_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2643_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_inc(v_head_2515_);
v___x_2520_ = l_Lean_Level_succ___override(v_head_2515_);
lean_inc(v_tail_2516_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v_tail_2516_);
v___x_2522_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_inc_ref(v___x_2522_);
v___x_2523_ = l_Lean_mkConst(v___x_2509_, v___x_2522_);
lean_inc(v_a_2493_);
lean_inc_ref(v_a_2492_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
lean_inc_ref(v___x_2523_);
v___x_2524_ = lean_infer_type(v___x_2523_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v___x_2526_ = l_Lean_mkSort(v_head_2515_);
v___x_2527_ = lean_box(v___x_2502_);
lean_inc_ref_n(v___x_2526_, 2);
v___f_2528_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2528_, 0, v___x_2526_);
lean_closure_set(v___f_2528_, 1, v___x_2527_);
v___x_2529_ = lean_box(v___y_2508_);
v___x_2530_ = lean_box(v___x_2502_);
v___f_2531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed), 17, 11);
lean_closure_set(v___f_2531_, 0, v_val_2499_);
lean_closure_set(v___f_2531_, 1, v___x_2523_);
lean_closure_set(v___f_2531_, 2, v___f_2528_);
lean_closure_set(v___f_2531_, 3, v___x_2506_);
lean_closure_set(v___f_2531_, 4, v_indName_2489_);
lean_closure_set(v___f_2531_, 5, v___x_2522_);
lean_closure_set(v___f_2531_, 6, v___x_2529_);
lean_closure_set(v___f_2531_, 7, v_tail_2516_);
lean_closure_set(v___f_2531_, 8, v___x_2526_);
lean_closure_set(v___f_2531_, 9, v___x_2530_);
lean_closure_set(v___f_2531_, 10, v_a_2525_);
v___x_2532_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_2533_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2532_, v___x_2526_, v___f_2531_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc_n(v_a_2534_, 2);
lean_dec_ref_known(v___x_2533_, 1);
lean_inc(v_a_2493_);
lean_inc_ref(v_a_2492_);
lean_inc(v_a_2491_);
lean_inc_ref(v_a_2490_);
v___x_2535_ = lean_infer_type(v_a_2534_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2617_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_box(1);
lean_inc(v_declName_2495_);
v___x_2538_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_declName_2495_, v_levelParams_2512_, v_a_2536_, v_a_2534_, v___x_2537_, v_a_2493_);
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2617_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2617_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set_tag(v___x_2541_, 1);
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
uint8_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = 0;
v___x_2546_ = l_Lean_addDecl(v___x_2544_, v___x_2545_, v_a_2492_, v_a_2493_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; lean_object* v_env_2548_; lean_object* v_nextMacroScope_2549_; lean_object* v_ngen_2550_; lean_object* v_auxDeclNGen_2551_; lean_object* v_traceState_2552_; lean_object* v_messages_2553_; lean_object* v_infoState_2554_; lean_object* v_snapshotTasks_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref_known(v___x_2546_, 1);
v___x_2547_ = lean_st_ref_take(v_a_2493_);
v_env_2548_ = lean_ctor_get(v___x_2547_, 0);
v_nextMacroScope_2549_ = lean_ctor_get(v___x_2547_, 1);
v_ngen_2550_ = lean_ctor_get(v___x_2547_, 2);
v_auxDeclNGen_2551_ = lean_ctor_get(v___x_2547_, 3);
v_traceState_2552_ = lean_ctor_get(v___x_2547_, 4);
v_messages_2553_ = lean_ctor_get(v___x_2547_, 6);
v_infoState_2554_ = lean_ctor_get(v___x_2547_, 7);
v_snapshotTasks_2555_ = lean_ctor_get(v___x_2547_, 8);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2547_, 5);
lean_dec(v_unused_2615_);
v___x_2557_ = v___x_2547_;
v_isShared_2558_ = v_isSharedCheck_2614_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_snapshotTasks_2555_);
lean_inc(v_infoState_2554_);
lean_inc(v_messages_2553_);
lean_inc(v_traceState_2552_);
lean_inc(v_auxDeclNGen_2551_);
lean_inc(v_ngen_2550_);
lean_inc(v_nextMacroScope_2549_);
lean_inc(v_env_2548_);
lean_dec(v___x_2547_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2614_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
lean_inc(v_declName_2495_);
v___x_2559_ = l_Lean_Meta_addToCompletionBlackList(v_env_2548_, v_declName_2495_);
v___x_2560_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 5, v___x_2560_);
lean_ctor_set(v___x_2557_, 0, v___x_2559_);
v___x_2562_ = v___x_2557_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_nextMacroScope_2549_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_ngen_2550_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_auxDeclNGen_2551_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_traceState_2552_);
lean_ctor_set(v_reuseFailAlloc_2613_, 5, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_messages_2553_);
lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_infoState_2554_);
lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_snapshotTasks_2555_);
v___x_2562_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_mctx_2565_; lean_object* v_zetaDeltaFVarIds_2566_; lean_object* v_postponed_2567_; lean_object* v_diag_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2611_; 
v___x_2563_ = lean_st_ref_put(v_a_2493_, v___x_2562_);
v___x_2564_ = lean_st_ref_take(v_a_2491_);
v_mctx_2565_ = lean_ctor_get(v___x_2564_, 0);
v_zetaDeltaFVarIds_2566_ = lean_ctor_get(v___x_2564_, 2);
v_postponed_2567_ = lean_ctor_get(v___x_2564_, 3);
v_diag_2568_ = lean_ctor_get(v___x_2564_, 4);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2564_, 1);
lean_dec(v_unused_2612_);
v___x_2570_ = v___x_2564_;
v_isShared_2571_ = v_isSharedCheck_2611_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_diag_2568_);
lean_inc(v_postponed_2567_);
lean_inc(v_zetaDeltaFVarIds_2566_);
lean_inc(v_mctx_2565_);
lean_dec(v___x_2564_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2611_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
v___x_2572_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2572_);
v___x_2574_ = v___x_2570_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_mctx_2565_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_zetaDeltaFVarIds_2566_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_postponed_2567_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_diag_2568_);
v___x_2574_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v_env_2577_; lean_object* v_nextMacroScope_2578_; lean_object* v_ngen_2579_; lean_object* v_auxDeclNGen_2580_; lean_object* v_traceState_2581_; lean_object* v_messages_2582_; lean_object* v_infoState_2583_; lean_object* v_snapshotTasks_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2608_; 
v___x_2575_ = lean_st_ref_put(v_a_2491_, v___x_2574_);
v___x_2576_ = lean_st_ref_take(v_a_2493_);
v_env_2577_ = lean_ctor_get(v___x_2576_, 0);
v_nextMacroScope_2578_ = lean_ctor_get(v___x_2576_, 1);
v_ngen_2579_ = lean_ctor_get(v___x_2576_, 2);
v_auxDeclNGen_2580_ = lean_ctor_get(v___x_2576_, 3);
v_traceState_2581_ = lean_ctor_get(v___x_2576_, 4);
v_messages_2582_ = lean_ctor_get(v___x_2576_, 6);
v_infoState_2583_ = lean_ctor_get(v___x_2576_, 7);
v_snapshotTasks_2584_ = lean_ctor_get(v___x_2576_, 8);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2576_, 5);
lean_dec(v_unused_2609_);
v___x_2586_ = v___x_2576_;
v_isShared_2587_ = v_isSharedCheck_2608_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_snapshotTasks_2584_);
lean_inc(v_infoState_2583_);
lean_inc(v_messages_2582_);
lean_inc(v_traceState_2581_);
lean_inc(v_auxDeclNGen_2580_);
lean_inc(v_ngen_2579_);
lean_inc(v_nextMacroScope_2578_);
lean_inc(v_env_2577_);
lean_dec(v___x_2576_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2608_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2590_; 
lean_inc(v_declName_2495_);
v___x_2588_ = l_Lean_addProtected(v_env_2577_, v_declName_2495_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 5, v___x_2560_);
lean_ctor_set(v___x_2586_, 0, v___x_2588_);
v___x_2590_ = v___x_2586_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_nextMacroScope_2578_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_ngen_2579_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_auxDeclNGen_2580_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_traceState_2581_);
lean_ctor_set(v_reuseFailAlloc_2607_, 5, v___x_2560_);
lean_ctor_set(v_reuseFailAlloc_2607_, 6, v_messages_2582_);
lean_ctor_set(v_reuseFailAlloc_2607_, 7, v_infoState_2583_);
lean_ctor_set(v_reuseFailAlloc_2607_, 8, v_snapshotTasks_2584_);
v___x_2590_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v_mctx_2593_; lean_object* v_zetaDeltaFVarIds_2594_; lean_object* v_postponed_2595_; lean_object* v_diag_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
v___x_2591_ = lean_st_ref_put(v_a_2493_, v___x_2590_);
v___x_2592_ = lean_st_ref_take(v_a_2491_);
v_mctx_2593_ = lean_ctor_get(v___x_2592_, 0);
v_zetaDeltaFVarIds_2594_ = lean_ctor_get(v___x_2592_, 2);
v_postponed_2595_ = lean_ctor_get(v___x_2592_, 3);
v_diag_2596_ = lean_ctor_get(v___x_2592_, 4);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2605_ == 0)
{
lean_object* v_unused_2606_; 
v_unused_2606_ = lean_ctor_get(v___x_2592_, 1);
lean_dec(v_unused_2606_);
v___x_2598_ = v___x_2592_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_diag_2596_);
lean_inc(v_postponed_2595_);
lean_inc(v_zetaDeltaFVarIds_2594_);
lean_inc(v_mctx_2593_);
lean_dec(v___x_2592_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 1, v___x_2572_);
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_mctx_2593_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2604_, 2, v_zetaDeltaFVarIds_2594_);
lean_ctor_set(v_reuseFailAlloc_2604_, 3, v_postponed_2595_);
lean_ctor_set(v_reuseFailAlloc_2604_, 4, v_diag_2596_);
v___x_2601_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_st_ref_put(v_a_2491_, v___x_2601_);
v___x_2603_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2495_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
return v___x_2603_;
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
lean_dec(v_declName_2495_);
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v_a_2534_);
lean_dec(v_levelParams_2512_);
lean_dec(v_declName_2495_);
v_a_2618_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2535_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2535_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec(v_levelParams_2512_);
lean_dec(v_declName_2495_);
v_a_2626_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2533_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2533_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v___x_2523_);
lean_dec_ref(v___x_2522_);
lean_dec(v_tail_2516_);
lean_dec(v_head_2515_);
lean_dec(v_levelParams_2512_);
lean_dec(v___x_2506_);
lean_dec_ref(v_val_2499_);
lean_dec(v_declName_2495_);
lean_dec(v_indName_2489_);
v_a_2634_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2524_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2524_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
}
}
else
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec(v___x_2514_);
lean_dec(v_levelParams_2512_);
lean_dec(v___x_2509_);
lean_dec(v___x_2506_);
lean_dec_ref(v_val_2499_);
lean_dec(v_declName_2495_);
lean_dec(v_indName_2489_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5);
v___x_2645_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2644_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
return v___x_2645_;
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v___x_2509_);
lean_dec(v___x_2506_);
lean_dec_ref(v_val_2499_);
lean_dec(v_declName_2495_);
lean_dec(v_indName_2489_);
v_a_2646_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2510_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2510_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec(v_a_2497_);
lean_dec(v_declName_2495_);
lean_dec(v_indName_2489_);
v___x_2658_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6);
v___x_2659_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2658_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
return v___x_2659_;
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_declName_2495_);
lean_dec(v_indName_2489_);
v_a_2660_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2496_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2496_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___boxed(lean_object* v_indName_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_indName_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(lean_object* v_i_2675_, lean_object* v_P_2676_, lean_object* v___x_2677_, lean_object* v_xs1_2678_, lean_object* v_zs1_2679_, lean_object* v_xs2_2680_, lean_object* v_as_2681_, size_t v_sz_2682_, size_t v_i_2683_, lean_object* v_bs_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_2675_, v_P_2676_, v___x_2677_, v_xs1_2678_, v_zs1_2679_, v_xs2_2680_, v_sz_2682_, v_i_2683_, v_bs_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___boxed(lean_object* v_i_2691_, lean_object* v_P_2692_, lean_object* v___x_2693_, lean_object* v_xs1_2694_, lean_object* v_zs1_2695_, lean_object* v_xs2_2696_, lean_object* v_as_2697_, lean_object* v_sz_2698_, lean_object* v_i_2699_, lean_object* v_bs_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
size_t v_sz_boxed_2706_; size_t v_i_boxed_2707_; lean_object* v_res_2708_; 
v_sz_boxed_2706_ = lean_unbox_usize(v_sz_2698_);
lean_dec(v_sz_2698_);
v_i_boxed_2707_ = lean_unbox_usize(v_i_2699_);
lean_dec(v_i_2699_);
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(v_i_2691_, v_P_2692_, v___x_2693_, v_xs1_2694_, v_zs1_2695_, v_xs2_2696_, v_as_2697_, v_sz_boxed_2706_, v_i_boxed_2707_, v_bs_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec_ref(v_as_2697_);
lean_dec(v_i_2691_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(lean_object* v_val_2709_, lean_object* v_P_2710_, lean_object* v_xs1_2711_, lean_object* v_xs2_2712_, lean_object* v_indName_2713_, lean_object* v___x_2714_, lean_object* v___x_2715_, lean_object* v_ysx2_2716_, uint8_t v___y_2717_, lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v_tail_2720_, lean_object* v___x_2721_, lean_object* v_as_2722_, size_t v_sz_2723_, size_t v_i_2724_, lean_object* v_bs_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_2709_, v_P_2710_, v_xs1_2711_, v_xs2_2712_, v_indName_2713_, v___x_2714_, v___x_2715_, v_ysx2_2716_, v___y_2717_, v___x_2718_, v___x_2719_, v_tail_2720_, v___x_2721_, v_sz_2723_, v_i_2724_, v_bs_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___boxed(lean_object** _args){
lean_object* v_val_2732_ = _args[0];
lean_object* v_P_2733_ = _args[1];
lean_object* v_xs1_2734_ = _args[2];
lean_object* v_xs2_2735_ = _args[3];
lean_object* v_indName_2736_ = _args[4];
lean_object* v___x_2737_ = _args[5];
lean_object* v___x_2738_ = _args[6];
lean_object* v_ysx2_2739_ = _args[7];
lean_object* v___y_2740_ = _args[8];
lean_object* v___x_2741_ = _args[9];
lean_object* v___x_2742_ = _args[10];
lean_object* v_tail_2743_ = _args[11];
lean_object* v___x_2744_ = _args[12];
lean_object* v_as_2745_ = _args[13];
lean_object* v_sz_2746_ = _args[14];
lean_object* v_i_2747_ = _args[15];
lean_object* v_bs_2748_ = _args[16];
lean_object* v___y_2749_ = _args[17];
lean_object* v___y_2750_ = _args[18];
lean_object* v___y_2751_ = _args[19];
lean_object* v___y_2752_ = _args[20];
lean_object* v___y_2753_ = _args[21];
_start:
{
uint8_t v___y_18326__boxed_2754_; size_t v_sz_boxed_2755_; size_t v_i_boxed_2756_; lean_object* v_res_2757_; 
v___y_18326__boxed_2754_ = lean_unbox(v___y_2740_);
v_sz_boxed_2755_ = lean_unbox_usize(v_sz_2746_);
lean_dec(v_sz_2746_);
v_i_boxed_2756_ = lean_unbox_usize(v_i_2747_);
lean_dec(v_i_2747_);
v_res_2757_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(v_val_2732_, v_P_2733_, v_xs1_2734_, v_xs2_2735_, v_indName_2736_, v___x_2737_, v___x_2738_, v_ysx2_2739_, v___y_18326__boxed_2754_, v___x_2741_, v___x_2742_, v_tail_2743_, v___x_2744_, v_as_2745_, v_sz_boxed_2755_, v_i_boxed_2756_, v_bs_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v_as_2745_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(lean_object* v_declName_2758_, uint8_t v_s_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2758_, v_s_2759_, v___y_2761_, v___y_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___boxed(lean_object* v_declName_2766_, lean_object* v_s_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
uint8_t v_s_boxed_2773_; lean_object* v_res_2774_; 
v_s_boxed_2773_ = lean_unbox(v_s_2767_);
v_res_2774_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(v_declName_2766_, v_s_boxed_2773_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(lean_object* v_00_u03b1_2775_, lean_object* v_constName_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_constName_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(v_00_u03b1_2783_, v_constName_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2791_, lean_object* v_ref_2792_, lean_object* v_constName_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2792_, v_constName_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_ref_2801_, lean_object* v_constName_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(v_00_u03b1_2800_, v_ref_2801_, v_constName_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v_ref_2801_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_2809_, lean_object* v_ref_2810_, lean_object* v_msg_2811_, lean_object* v_declHint_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; 
v___x_2818_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2810_, v_msg_2811_, v_declHint_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_ref_2820_, lean_object* v_msg_2821_, lean_object* v_declHint_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_2819_, v_ref_2820_, v_msg_2821_, v_declHint_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_ref_2820_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_2829_, lean_object* v_declHint_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2829_, v_declHint_2830_, v___y_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_2837_, lean_object* v_declHint_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_2837_, v_declHint_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_2845_, lean_object* v_ref_2846_, lean_object* v_msg_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2846_, v_msg_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_2854_, lean_object* v_ref_2855_, lean_object* v_msg_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_2854_, v_ref_2855_, v_msg_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v_ref_2855_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_2863_, lean_object* v_xs_2864_, lean_object* v_k_2865_, lean_object* v_tail_2866_, lean_object* v_tail_2867_, lean_object* v_v_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(v_x_2863_, v_xs_2864_, v_k_2865_, v_tail_2866_, v_tail_2867_, v_v_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(lean_object* v_xs_2878_, lean_object* v_k_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
if (lean_obj_tag(v_x_2880_) == 1)
{
if (lean_obj_tag(v_x_2881_) == 1)
{
lean_object* v_head_2888_; lean_object* v_tail_2889_; lean_object* v_head_2890_; lean_object* v_tail_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; 
v_head_2888_ = lean_ctor_get(v_x_2880_, 0);
lean_inc(v_head_2888_);
v_tail_2889_ = lean_ctor_get(v_x_2880_, 1);
lean_inc(v_tail_2889_);
lean_dec_ref_known(v_x_2880_, 2);
v_head_2890_ = lean_ctor_get(v_x_2881_, 0);
lean_inc(v_head_2890_);
v_tail_2891_ = lean_ctor_get(v_x_2881_, 1);
lean_inc(v_tail_2891_);
lean_dec_ref_known(v_x_2881_, 2);
lean_inc_ref(v_xs_2878_);
lean_inc_ref(v_x_2882_);
v___f_2892_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2892_, 0, v_x_2882_);
lean_closure_set(v___f_2892_, 1, v_xs_2878_);
lean_closure_set(v___f_2892_, 2, v_k_2879_);
lean_closure_set(v___f_2892_, 3, v_tail_2889_);
lean_closure_set(v___f_2892_, 4, v_tail_2891_);
v___x_2893_ = l_Lean_Meta_mkEqHEq(v_head_2888_, v_head_2890_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = lean_array_get_size(v_xs_2878_);
lean_dec_ref(v_xs_2878_);
v___x_2897_ = lean_nat_dec_lt(v___x_2895_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
lean_dec_ref(v_x_2882_);
v___x_2898_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2899_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2898_, v_a_2894_, v___f_2892_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2900_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2901_ = lean_array_get_size(v_x_2882_);
lean_dec_ref(v_x_2882_);
v___x_2902_ = lean_nat_add(v___x_2901_, v___x_2895_);
v___x_2903_ = lean_name_append_index_after(v___x_2900_, v___x_2902_);
v___x_2904_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2903_, v_a_2894_, v___f_2892_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
return v___x_2904_;
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v___f_2892_);
lean_dec_ref(v_x_2882_);
lean_dec_ref(v_xs_2878_);
v_a_2905_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2893_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2893_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v___x_2913_; 
lean_dec_ref_known(v_x_2880_, 2);
lean_dec(v_x_2881_);
lean_dec_ref(v_xs_2878_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
v___x_2913_ = lean_apply_6(v_k_2879_, v_x_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, lean_box(0));
return v___x_2913_;
}
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_x_2881_);
lean_dec(v_x_2880_);
lean_dec_ref(v_xs_2878_);
lean_inc(v_a_2886_);
lean_inc_ref(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc_ref(v_a_2883_);
v___x_2914_ = lean_apply_6(v_k_2879_, v_x_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, lean_box(0));
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(lean_object* v_x_2915_, lean_object* v_xs_2916_, lean_object* v_k_2917_, lean_object* v_tail_2918_, lean_object* v_tail_2919_, lean_object* v_v_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_array_push(v_x_2915_, v_v_2920_);
v___x_2927_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2916_, v_k_2917_, v_tail_2918_, v_tail_2919_, v___x_2926_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___boxed(lean_object* v_xs_2928_, lean_object* v_k_2929_, lean_object* v_x_2930_, lean_object* v_x_2931_, lean_object* v_x_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2928_, v_k_2929_, v_x_2930_, v_x_2931_, v_x_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(lean_object* v_00_u03b1_2939_, lean_object* v_xs_2940_, lean_object* v_k_2941_, lean_object* v_x_2942_, lean_object* v_x_2943_, lean_object* v_x_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v___x_2950_; 
v___x_2950_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2940_, v_k_2941_, v_x_2942_, v_x_2943_, v_x_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___boxed(lean_object* v_00_u03b1_2951_, lean_object* v_xs_2952_, lean_object* v_k_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_, lean_object* v_x_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(v_00_u03b1_2951_, v_xs_2952_, v_k_2953_, v_x_2954_, v_x_2955_, v_x_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(lean_object* v_xs_2965_, lean_object* v_ys_2966_, lean_object* v_k_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_inc_ref(v_xs_2965_);
v___x_2973_ = lean_array_to_list(v_xs_2965_);
v___x_2974_ = lean_array_to_list(v_ys_2966_);
v___x_2975_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_2976_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2965_, v_k_2967_, v___x_2973_, v___x_2974_, v___x_2975_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___boxed(lean_object* v_xs_2977_, lean_object* v_ys_2978_, lean_object* v_k_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2977_, v_ys_2978_, v_k_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(lean_object* v_00_u03b1_2986_, lean_object* v_inst_2987_, lean_object* v_xs_2988_, lean_object* v_ys_2989_, lean_object* v_k_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2988_, v_ys_2989_, v_k_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___boxed(lean_object* v_00_u03b1_2997_, lean_object* v_inst_2998_, lean_object* v_xs_2999_, lean_object* v_ys_3000_, lean_object* v_k_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(v_00_u03b1_2997_, v_inst_2998_, v_xs_2999_, v_ys_3000_, v_k_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
lean_dec(v_a_3003_);
lean_dec_ref(v_a_3002_);
lean_dec(v_inst_2998_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_3008_, lean_object* v_x_3009_, lean_object* v_xs_3010_, lean_object* v_k_3011_, lean_object* v_tail_3012_, lean_object* v_tail_3013_, lean_object* v_v_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(v_x_3008_, v_x_3009_, v_xs_3010_, v_k_3011_, v_tail_3012_, v_tail_3013_, v_v_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(lean_object* v_xs_3021_, lean_object* v_k_3022_, lean_object* v_x_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
if (lean_obj_tag(v_x_3023_) == 1)
{
if (lean_obj_tag(v_x_3024_) == 1)
{
lean_object* v_head_3032_; lean_object* v_tail_3033_; lean_object* v_head_3034_; lean_object* v_tail_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; 
v_head_3032_ = lean_ctor_get(v_x_3023_, 0);
lean_inc_n(v_head_3032_, 2);
v_tail_3033_ = lean_ctor_get(v_x_3023_, 1);
lean_inc_n(v_tail_3033_, 2);
lean_dec_ref_known(v_x_3023_, 2);
v_head_3034_ = lean_ctor_get(v_x_3024_, 0);
lean_inc_n(v_head_3034_, 2);
v_tail_3035_ = lean_ctor_get(v_x_3024_, 1);
lean_inc_n(v_tail_3035_, 2);
lean_dec_ref_known(v_x_3024_, 2);
lean_inc_ref(v_k_3022_);
lean_inc_ref(v_xs_3021_);
lean_inc_ref(v_x_3026_);
lean_inc_ref(v_x_3025_);
v___f_3036_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3036_, 0, v_x_3025_);
lean_closure_set(v___f_3036_, 1, v_x_3026_);
lean_closure_set(v___f_3036_, 2, v_xs_3021_);
lean_closure_set(v___f_3036_, 3, v_k_3022_);
lean_closure_set(v___f_3036_, 4, v_tail_3033_);
lean_closure_set(v___f_3036_, 5, v_tail_3035_);
v___x_3037_ = l_Lean_Meta_isExprDefEq(v_head_3032_, v_head_3034_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; uint8_t v___x_3060_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3060_ = l_List_isEmpty___redArg(v_tail_3033_);
if (v___x_3060_ == 0)
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_unbox(v_a_3038_);
lean_dec(v_a_3038_);
if (v___x_3061_ == 0)
{
lean_dec(v_tail_3035_);
lean_dec(v_tail_3033_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_k_3022_);
goto v___jp_3039_;
}
else
{
lean_object* v___x_3062_; 
lean_dec_ref(v___f_3036_);
lean_dec(v_head_3034_);
v___x_3062_ = l_Lean_Meta_mkEqRefl(v_head_3032_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = lean_array_push(v_x_3026_, v_a_3063_);
v_x_3023_ = v_tail_3033_;
v_x_3024_ = v_tail_3035_;
v_x_3026_ = v___x_3064_;
goto _start;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_tail_3035_);
lean_dec(v_tail_3033_);
lean_dec_ref(v_x_3026_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_k_3022_);
lean_dec_ref(v_xs_3021_);
v_a_3066_ = lean_ctor_get(v___x_3062_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3062_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3062_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
else
{
lean_dec(v_a_3038_);
lean_dec(v_tail_3035_);
lean_dec(v_tail_3033_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_k_3022_);
goto v___jp_3039_;
}
v___jp_3039_:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_Lean_Meta_mkEqHEq(v_head_3032_, v_head_3034_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = lean_array_get_size(v_xs_3021_);
lean_dec_ref(v_xs_3021_);
v___x_3044_ = lean_nat_dec_lt(v___x_3042_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_x_3026_);
v___x_3045_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3046_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3045_, v_a_3041_, v___f_3036_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
return v___x_3046_;
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3048_ = lean_array_get_size(v_x_3026_);
lean_dec_ref(v_x_3026_);
v___x_3049_ = lean_nat_add(v___x_3048_, v___x_3042_);
v___x_3050_ = lean_name_append_index_after(v___x_3047_, v___x_3049_);
v___x_3051_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3050_, v_a_3041_, v___f_3036_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
return v___x_3051_;
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v___f_3036_);
lean_dec_ref(v_x_3026_);
lean_dec_ref(v_xs_3021_);
v_a_3052_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3040_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3040_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v___f_3036_);
lean_dec(v_tail_3035_);
lean_dec(v_head_3034_);
lean_dec(v_tail_3033_);
lean_dec(v_head_3032_);
lean_dec_ref(v_x_3026_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_k_3022_);
lean_dec_ref(v_xs_3021_);
v_a_3074_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3037_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3037_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v___x_3082_; 
lean_dec_ref_known(v_x_3023_, 2);
lean_dec(v_x_3024_);
lean_dec_ref(v_xs_3021_);
lean_inc(v_a_3030_);
lean_inc_ref(v_a_3029_);
lean_inc(v_a_3028_);
lean_inc_ref(v_a_3027_);
v___x_3082_ = lean_apply_7(v_k_3022_, v_x_3025_, v_x_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, lean_box(0));
return v___x_3082_;
}
}
else
{
lean_object* v___x_3083_; 
lean_dec(v_x_3024_);
lean_dec(v_x_3023_);
lean_dec_ref(v_xs_3021_);
lean_inc(v_a_3030_);
lean_inc_ref(v_a_3029_);
lean_inc(v_a_3028_);
lean_inc_ref(v_a_3027_);
v___x_3083_ = lean_apply_7(v_k_3022_, v_x_3025_, v_x_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, lean_box(0));
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(lean_object* v_x_3084_, lean_object* v_x_3085_, lean_object* v_xs_3086_, lean_object* v_k_3087_, lean_object* v_tail_3088_, lean_object* v_tail_3089_, lean_object* v_v_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
lean_inc_ref(v_v_3090_);
v___x_3096_ = lean_array_push(v_x_3084_, v_v_3090_);
v___x_3097_ = lean_array_push(v_x_3085_, v_v_3090_);
v___x_3098_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3086_, v_k_3087_, v_tail_3088_, v_tail_3089_, v___x_3096_, v___x_3097_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___boxed(lean_object* v_xs_3099_, lean_object* v_k_3100_, lean_object* v_x_3101_, lean_object* v_x_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3099_, v_k_3100_, v_x_3101_, v_x_3102_, v_x_3103_, v_x_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_);
lean_dec(v_a_3108_);
lean_dec_ref(v_a_3107_);
lean_dec(v_a_3106_);
lean_dec_ref(v_a_3105_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(lean_object* v_00_u03b1_3111_, lean_object* v_xs_3112_, lean_object* v_k_3113_, lean_object* v_x_3114_, lean_object* v_x_3115_, lean_object* v_x_3116_, lean_object* v_x_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3112_, v_k_3113_, v_x_3114_, v_x_3115_, v_x_3116_, v_x_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___boxed(lean_object* v_00_u03b1_3124_, lean_object* v_xs_3125_, lean_object* v_k_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_, lean_object* v_x_3129_, lean_object* v_x_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(v_00_u03b1_3124_, v_xs_3125_, v_k_3126_, v_x_3127_, v_x_3128_, v_x_3129_, v_x_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(lean_object* v_xs_3137_, lean_object* v_ys_3138_, lean_object* v_k_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_inc_ref(v_xs_3137_);
v___x_3145_ = lean_array_to_list(v_xs_3137_);
v___x_3146_ = lean_array_to_list(v_ys_3138_);
v___x_3147_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_3148_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3137_, v_k_3139_, v___x_3145_, v___x_3146_, v___x_3147_, v___x_3147_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg___boxed(lean_object* v_xs_3149_, lean_object* v_ys_3150_, lean_object* v_k_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3149_, v_ys_3150_, v_k_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(lean_object* v_00_u03b1_3158_, lean_object* v_inst_3159_, lean_object* v_xs_3160_, lean_object* v_ys_3161_, lean_object* v_k_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3160_, v_ys_3161_, v_k_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___boxed(lean_object* v_00_u03b1_3169_, lean_object* v_inst_3170_, lean_object* v_xs_3171_, lean_object* v_ys_3172_, lean_object* v_k_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(v_00_u03b1_3169_, v_inst_3170_, v_xs_3171_, v_ys_3172_, v_k_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec(v_inst_3170_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(lean_object* v_mvarId_3180_, lean_object* v_x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3180_, v_x_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3187_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3187_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg___boxed(lean_object* v_mvarId_3204_, lean_object* v_x_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3204_, v_x_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(lean_object* v_00_u03b1_3212_, lean_object* v_mvarId_3213_, lean_object* v_x_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3213_, v_x_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___boxed(lean_object* v_00_u03b1_3221_, lean_object* v_mvarId_3222_, lean_object* v_x_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(v_00_u03b1_3221_, v_mvarId_3222_, v_x_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(lean_object* v_msg_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___f_3236_; lean_object* v___x_3633__overap_3237_; lean_object* v___x_3238_; 
v___f_3236_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_3633__overap_3237_ = lean_panic_fn_borrowed(v___f_3236_, v_msg_3230_);
lean_inc(v___y_3234_);
lean_inc_ref(v___y_3233_);
lean_inc(v___y_3232_);
lean_inc_ref(v___y_3231_);
v___x_3238_ = lean_apply_5(v___x_3633__overap_3237_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, lean_box(0));
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2___boxed(lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(v_msg_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(lean_object* v_e_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v___x_3249_; 
v___x_3249_ = l_Lean_Expr_hasMVar(v_e_3246_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3250_, 0, v_e_3246_);
return v___x_3250_;
}
else
{
lean_object* v___x_3251_; lean_object* v_mctx_3252_; lean_object* v___x_3253_; lean_object* v_fst_3254_; lean_object* v_snd_3255_; lean_object* v___x_3256_; lean_object* v_cache_3257_; lean_object* v_zetaDeltaFVarIds_3258_; lean_object* v_postponed_3259_; lean_object* v_diag_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3269_; 
v___x_3251_ = lean_st_ref_get(v___y_3247_);
v_mctx_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc_ref(v_mctx_3252_);
lean_dec(v___x_3251_);
v___x_3253_ = l_Lean_instantiateMVarsCore(v_mctx_3252_, v_e_3246_);
v_fst_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_fst_3254_);
v_snd_3255_ = lean_ctor_get(v___x_3253_, 1);
lean_inc(v_snd_3255_);
lean_dec_ref(v___x_3253_);
v___x_3256_ = lean_st_ref_take(v___y_3247_);
v_cache_3257_ = lean_ctor_get(v___x_3256_, 1);
v_zetaDeltaFVarIds_3258_ = lean_ctor_get(v___x_3256_, 2);
v_postponed_3259_ = lean_ctor_get(v___x_3256_, 3);
v_diag_3260_ = lean_ctor_get(v___x_3256_, 4);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3269_ == 0)
{
lean_object* v_unused_3270_; 
v_unused_3270_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3270_);
v___x_3262_ = v___x_3256_;
v_isShared_3263_ = v_isSharedCheck_3269_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_diag_3260_);
lean_inc(v_postponed_3259_);
lean_inc(v_zetaDeltaFVarIds_3258_);
lean_inc(v_cache_3257_);
lean_dec(v___x_3256_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3269_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
lean_ctor_set(v___x_3262_, 0, v_snd_3255_);
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_snd_3255_);
lean_ctor_set(v_reuseFailAlloc_3268_, 1, v_cache_3257_);
lean_ctor_set(v_reuseFailAlloc_3268_, 2, v_zetaDeltaFVarIds_3258_);
lean_ctor_set(v_reuseFailAlloc_3268_, 3, v_postponed_3259_);
lean_ctor_set(v_reuseFailAlloc_3268_, 4, v_diag_3260_);
v___x_3265_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = lean_st_ref_put(v___y_3247_, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3267_, 0, v_fst_3254_);
return v___x_3267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg___boxed(lean_object* v_e_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3271_, v___y_3272_);
lean_dec(v___y_3272_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(lean_object* v_e_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3275_, v___y_3277_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___boxed(lean_object* v_e_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(v_e_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(lean_object* v_cls_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v_toCold_3298_; lean_object* v_options_3299_; uint8_t v_hasTrace_3300_; 
v_toCold_3298_ = lean_ctor_get(v___y_3295_, 0);
v_options_3299_ = lean_ctor_get(v_toCold_3298_, 2);
v_hasTrace_3300_ = lean_ctor_get_uint8(v_options_3299_, sizeof(void*)*1);
if (v_hasTrace_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
lean_dec(v_cls_3292_);
v___x_3301_ = lean_box(v_hasTrace_3300_);
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
return v___x_3302_;
}
else
{
lean_object* v_inheritedTraceOptions_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_inheritedTraceOptions_3303_ = lean_ctor_get(v_toCold_3298_, 11);
v___x_3304_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
v___x_3305_ = l_Lean_Name_append(v___x_3304_, v_cls_3292_);
v___x_3306_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3303_, v_options_3299_, v___x_3305_);
lean_dec(v___x_3305_);
v___x_3307_ = lean_box(v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___boxed(lean_object* v_cls_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(v_cls_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
return v_res_3315_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3316_; double v___x_3317_; 
v___x_3316_ = lean_unsigned_to_nat(0u);
v___x_3317_ = lean_float_of_nat(v___x_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(lean_object* v_cls_3321_, lean_object* v_msg_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_ref_3328_; lean_object* v___x_3329_; lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3374_; 
v_ref_3328_ = lean_ctor_get(v___y_3325_, 2);
v___x_3329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3374_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3374_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v_traceState_3335_; lean_object* v_env_3336_; lean_object* v_nextMacroScope_3337_; lean_object* v_ngen_3338_; lean_object* v_auxDeclNGen_3339_; lean_object* v_cache_3340_; lean_object* v_messages_3341_; lean_object* v_infoState_3342_; lean_object* v_snapshotTasks_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3373_; 
v___x_3334_ = lean_st_ref_take(v___y_3326_);
v_traceState_3335_ = lean_ctor_get(v___x_3334_, 4);
v_env_3336_ = lean_ctor_get(v___x_3334_, 0);
v_nextMacroScope_3337_ = lean_ctor_get(v___x_3334_, 1);
v_ngen_3338_ = lean_ctor_get(v___x_3334_, 2);
v_auxDeclNGen_3339_ = lean_ctor_get(v___x_3334_, 3);
v_cache_3340_ = lean_ctor_get(v___x_3334_, 5);
v_messages_3341_ = lean_ctor_get(v___x_3334_, 6);
v_infoState_3342_ = lean_ctor_get(v___x_3334_, 7);
v_snapshotTasks_3343_ = lean_ctor_get(v___x_3334_, 8);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3345_ = v___x_3334_;
v_isShared_3346_ = v_isSharedCheck_3373_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snapshotTasks_3343_);
lean_inc(v_infoState_3342_);
lean_inc(v_messages_3341_);
lean_inc(v_cache_3340_);
lean_inc(v_traceState_3335_);
lean_inc(v_auxDeclNGen_3339_);
lean_inc(v_ngen_3338_);
lean_inc(v_nextMacroScope_3337_);
lean_inc(v_env_3336_);
lean_dec(v___x_3334_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3373_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint64_t v_tid_3347_; lean_object* v_traces_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3372_; 
v_tid_3347_ = lean_ctor_get_uint64(v_traceState_3335_, sizeof(void*)*1);
v_traces_3348_ = lean_ctor_get(v_traceState_3335_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_traceState_3335_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3350_ = v_traceState_3335_;
v_isShared_3351_ = v_isSharedCheck_3372_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_traces_3348_);
lean_dec(v_traceState_3335_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3372_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; double v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
v___x_3355_ = 0;
v___x_3356_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_3357_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3357_, 0, v_cls_3321_);
lean_ctor_set(v___x_3357_, 1, v___x_3353_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
lean_ctor_set_float(v___x_3357_, sizeof(void*)*3, v___x_3354_);
lean_ctor_set_float(v___x_3357_, sizeof(void*)*3 + 8, v___x_3354_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3 + 16, v___x_3355_);
v___x_3358_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2));
v___x_3359_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v_a_3330_);
lean_ctor_set(v___x_3359_, 2, v___x_3358_);
lean_inc(v_ref_3328_);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_ref_3328_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_PersistentArray_push___redArg(v_traces_3348_, v___x_3360_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3361_);
v___x_3363_ = v___x_3350_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3361_);
lean_ctor_set_uint64(v_reuseFailAlloc_3371_, sizeof(void*)*1, v_tid_3347_);
v___x_3363_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 4, v___x_3363_);
v___x_3365_ = v___x_3345_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_env_3336_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_nextMacroScope_3337_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_ngen_3338_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_auxDeclNGen_3339_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3370_, 5, v_cache_3340_);
lean_ctor_set(v_reuseFailAlloc_3370_, 6, v_messages_3341_);
lean_ctor_set(v_reuseFailAlloc_3370_, 7, v_infoState_3342_);
lean_ctor_set(v_reuseFailAlloc_3370_, 8, v_snapshotTasks_3343_);
v___x_3365_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_st_ref_put(v___y_3326_, v___x_3365_);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 0, v___x_3352_);
v___x_3368_ = v___x_3332_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3352_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___boxed(lean_object* v_cls_3375_, lean_object* v_msg_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3375_, v_msg_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(lean_object* v___f_3392_, lean_object* v___x_3393_, lean_object* v_fst_3394_, lean_object* v_cls_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; 
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
v___x_3401_ = lean_apply_5(v___f_3392_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, lean_box(0));
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3433_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3404_ = v___x_3401_;
v_isShared_3405_ = v_isSharedCheck_3433_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3401_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3433_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
uint8_t v___x_3406_; 
v___x_3406_ = lean_unbox(v_a_3402_);
lean_dec(v_a_3402_);
if (v___x_3406_ == 0)
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v_cls_3395_);
lean_dec(v_fst_3394_);
lean_dec_ref(v___x_3393_);
v___x_3407_ = lean_box(0);
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v___x_3407_);
v___x_3409_ = v___x_3404_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3407_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
else
{
lean_object* v___x_3411_; 
lean_del_object(v___x_3404_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___x_3393_);
v___x_3411_ = lean_infer_type(v___x_3393_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1);
v___x_3414_ = l_Lean_MessageData_ofExpr(v___x_3393_);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = l_Lean_MessageData_ofExpr(v_a_3412_);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_fst_3394_);
v___x_3423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3395_, v___x_3423_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
return v___x_3424_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v_cls_3395_);
lean_dec(v_fst_3394_);
lean_dec_ref(v___x_3393_);
v_a_3425_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3411_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3411_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v_cls_3395_);
lean_dec(v_fst_3394_);
lean_dec_ref(v___x_3393_);
v_a_3434_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3401_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3401_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed(lean_object* v___f_3442_, lean_object* v___x_3443_, lean_object* v_fst_3444_, lean_object* v_cls_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(v___f_3442_, v___x_3443_, v_fst_3444_, v_cls_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
return v_res_3451_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0));
v___x_3454_ = l_Lean_stringToMessageData(v___x_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(lean_object* v_cls_3455_, lean_object* v___x_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_toCold_3465_; lean_object* v_options_3466_; uint8_t v_hasTrace_3467_; 
v_toCold_3465_ = lean_ctor_get(v___y_3459_, 0);
v_options_3466_ = lean_ctor_get(v_toCold_3465_, 2);
v_hasTrace_3467_ = lean_ctor_get_uint8(v_options_3466_, sizeof(void*)*1);
if (v_hasTrace_3467_ == 0)
{
lean_dec_ref(v___x_3456_);
lean_dec(v_cls_3455_);
goto v___jp_3462_;
}
else
{
lean_object* v_inheritedTraceOptions_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v_inheritedTraceOptions_3468_ = lean_ctor_get(v_toCold_3465_, 11);
v___x_3469_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
lean_inc(v_cls_3455_);
v___x_3470_ = l_Lean_Name_append(v___x_3469_, v_cls_3455_);
v___x_3471_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3468_, v_options_3466_, v___x_3470_);
lean_dec(v___x_3470_);
if (v___x_3471_ == 0)
{
lean_dec_ref(v___x_3456_);
lean_dec(v_cls_3455_);
goto v___jp_3462_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1);
v___x_3473_ = l_Lean_MessageData_ofExpr(v___x_3456_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3455_, v___x_3474_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
return v___x_3475_;
}
}
v___jp_3462_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
return v___x_3464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed(lean_object* v_cls_3476_, lean_object* v___x_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(v_cls_3476_, v___x_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(lean_object* v_as_3488_, size_t v_sz_3489_, size_t v_i_3490_, lean_object* v_b_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_usize_dec_lt(v_i_3490_, v_sz_3489_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v_b_3491_);
return v___x_3498_;
}
else
{
lean_object* v_fst_3499_; lean_object* v_snd_3500_; lean_object* v_cls_3501_; lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___f_3505_; lean_object* v___x_3506_; 
v_fst_3499_ = lean_ctor_get(v_b_3491_, 0);
lean_inc_n(v_fst_3499_, 2);
v_snd_3500_ = lean_ctor_get(v_b_3491_, 1);
lean_inc(v_snd_3500_);
lean_dec_ref(v_b_3491_);
v_cls_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v_a_3502_ = lean_array_uget_borrowed(v_as_3488_, v_i_3490_);
v___x_3503_ = l_Lean_Expr_fvarId_x21(v_a_3502_);
v___x_3504_ = l_Lean_Meta_FVarSubst_get(v_snd_3500_, v___x_3503_);
lean_inc_ref(v___x_3504_);
v___f_3505_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3505_, 0, v_cls_3501_);
lean_closure_set(v___f_3505_, 1, v___x_3504_);
v___x_3506_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_fst_3499_, v___f_3505_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec_ref_known(v___x_3506_, 1);
v___x_3507_ = l_Lean_Expr_fvarId_x21(v___x_3504_);
lean_dec_ref(v___x_3504_);
v___x_3508_ = l_Lean_Meta_substEq(v_fst_3499_, v___x_3507_, v_snd_3500_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v_fst_3510_; lean_object* v_snd_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3521_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v_fst_3510_ = lean_ctor_get(v_a_3509_, 0);
v_snd_3511_ = lean_ctor_get(v_a_3509_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_a_3509_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3513_ = v_a_3509_;
v_isShared_3514_ = v_isSharedCheck_3521_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_snd_3511_);
lean_inc(v_fst_3510_);
lean_dec(v_a_3509_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3521_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 1, v_fst_3510_);
lean_ctor_set(v___x_3513_, 0, v_snd_3511_);
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_snd_3511_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_fst_3510_);
v___x_3516_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
size_t v___x_3517_; size_t v___x_3518_; 
v___x_3517_ = ((size_t)1ULL);
v___x_3518_ = lean_usize_add(v_i_3490_, v___x_3517_);
v_i_3490_ = v___x_3518_;
v_b_3491_ = v___x_3516_;
goto _start;
}
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
v_a_3522_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3508_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3508_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v___x_3504_);
lean_dec(v_snd_3500_);
lean_dec(v_fst_3499_);
v_a_3530_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3506_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3506_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___boxed(lean_object* v_as_3538_, lean_object* v_sz_3539_, lean_object* v_i_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
size_t v_sz_boxed_3547_; size_t v_i_boxed_3548_; lean_object* v_res_3549_; 
v_sz_boxed_3547_ = lean_unbox_usize(v_sz_3539_);
lean_dec(v_sz_3539_);
v_i_boxed_3548_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(v_as_3538_, v_sz_boxed_3547_, v_i_boxed_3548_, v_b_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec_ref(v_as_3538_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_, lean_object* v_x_3553_){
_start:
{
lean_object* v_ks_3554_; lean_object* v_vs_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3579_; 
v_ks_3554_ = lean_ctor_get(v_x_3550_, 0);
v_vs_3555_ = lean_ctor_get(v_x_3550_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_x_3550_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3557_ = v_x_3550_;
v_isShared_3558_ = v_isSharedCheck_3579_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_vs_3555_);
lean_inc(v_ks_3554_);
lean_dec(v_x_3550_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3579_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3559_ = lean_array_get_size(v_ks_3554_);
v___x_3560_ = lean_nat_dec_lt(v_x_3551_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
lean_dec(v_x_3551_);
v___x_3561_ = lean_array_push(v_ks_3554_, v_x_3552_);
v___x_3562_ = lean_array_push(v_vs_3555_, v_x_3553_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3562_);
lean_ctor_set(v___x_3557_, 0, v___x_3561_);
v___x_3564_ = v___x_3557_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
else
{
lean_object* v_k_x27_3566_; uint8_t v___x_3567_; 
v_k_x27_3566_ = lean_array_fget_borrowed(v_ks_3554_, v_x_3551_);
v___x_3567_ = l_Lean_instBEqMVarId_beq(v_x_3552_, v_k_x27_3566_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3569_; 
if (v_isShared_3558_ == 0)
{
v___x_3569_ = v___x_3557_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_ks_3554_);
lean_ctor_set(v_reuseFailAlloc_3573_, 1, v_vs_3555_);
v___x_3569_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_unsigned_to_nat(1u);
v___x_3571_ = lean_nat_add(v_x_3551_, v___x_3570_);
lean_dec(v_x_3551_);
v_x_3550_ = v___x_3569_;
v_x_3551_ = v___x_3571_;
goto _start;
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3574_ = lean_array_fset(v_ks_3554_, v_x_3551_, v_x_3552_);
v___x_3575_ = lean_array_fset(v_vs_3555_, v_x_3551_, v_x_3553_);
lean_dec(v_x_3551_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3575_);
lean_ctor_set(v___x_3557_, 0, v___x_3574_);
v___x_3577_ = v___x_3557_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3575_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(lean_object* v_n_3580_, lean_object* v_k_3581_, lean_object* v_v_3582_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(v_n_3580_, v___x_3583_, v_k_3581_, v_v_3582_);
return v___x_3584_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(lean_object* v_x_3586_, size_t v_x_3587_, size_t v_x_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3586_) == 0)
{
lean_object* v_es_3591_; size_t v___x_3592_; size_t v___x_3593_; lean_object* v_j_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; 
v_es_3591_ = lean_ctor_get(v_x_3586_, 0);
v___x_3592_ = ((size_t)31ULL);
v___x_3593_ = lean_usize_land(v_x_3587_, v___x_3592_);
v_j_3594_ = lean_usize_to_nat(v___x_3593_);
v___x_3595_ = lean_array_get_size(v_es_3591_);
v___x_3596_ = lean_nat_dec_lt(v_j_3594_, v___x_3595_);
if (v___x_3596_ == 0)
{
lean_dec(v_j_3594_);
lean_dec(v_x_3590_);
lean_dec(v_x_3589_);
return v_x_3586_;
}
else
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3635_; 
lean_inc_ref(v_es_3591_);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_x_3586_);
if (v_isSharedCheck_3635_ == 0)
{
lean_object* v_unused_3636_; 
v_unused_3636_ = lean_ctor_get(v_x_3586_, 0);
lean_dec(v_unused_3636_);
v___x_3598_ = v_x_3586_;
v_isShared_3599_ = v_isSharedCheck_3635_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v_x_3586_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3635_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v_v_3600_; lean_object* v___x_3601_; lean_object* v_xs_x27_3602_; lean_object* v___y_3604_; 
v_v_3600_ = lean_array_fget(v_es_3591_, v_j_3594_);
v___x_3601_ = lean_box(0);
v_xs_x27_3602_ = lean_array_fset(v_es_3591_, v_j_3594_, v___x_3601_);
switch(lean_obj_tag(v_v_3600_))
{
case 0:
{
lean_object* v_key_3609_; lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3620_; 
v_key_3609_ = lean_ctor_get(v_v_3600_, 0);
v_val_3610_ = lean_ctor_get(v_v_3600_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_v_3600_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3612_ = v_v_3600_;
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_inc(v_key_3609_);
lean_dec(v_v_3600_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3620_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
uint8_t v___x_3614_; 
v___x_3614_ = l_Lean_instBEqMVarId_beq(v_x_3589_, v_key_3609_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
lean_del_object(v___x_3612_);
v___x_3615_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3609_, v_val_3610_, v_x_3589_, v_x_3590_);
v___x_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
v___y_3604_ = v___x_3616_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3618_; 
lean_dec(v_val_3610_);
lean_dec(v_key_3609_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v_x_3590_);
lean_ctor_set(v___x_3612_, 0, v_x_3589_);
v___x_3618_ = v___x_3612_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_x_3589_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_x_3590_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
v___y_3604_ = v___x_3618_;
goto v___jp_3603_;
}
}
}
}
case 1:
{
lean_object* v_node_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3633_; 
v_node_3621_ = lean_ctor_get(v_v_3600_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_v_3600_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3623_ = v_v_3600_;
v_isShared_3624_ = v_isSharedCheck_3633_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_node_3621_);
lean_dec(v_v_3600_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3633_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
size_t v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; size_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3625_ = ((size_t)5ULL);
v___x_3626_ = lean_usize_shift_right(v_x_3587_, v___x_3625_);
v___x_3627_ = ((size_t)1ULL);
v___x_3628_ = lean_usize_add(v_x_3588_, v___x_3627_);
v___x_3629_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_node_3621_, v___x_3626_, v___x_3628_, v_x_3589_, v_x_3590_);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3629_);
v___x_3631_ = v___x_3623_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
v___y_3604_ = v___x_3631_;
goto v___jp_3603_;
}
}
}
default: 
{
lean_object* v___x_3634_; 
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v_x_3589_);
lean_ctor_set(v___x_3634_, 1, v_x_3590_);
v___y_3604_ = v___x_3634_;
goto v___jp_3603_;
}
}
v___jp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = lean_array_fset(v_xs_x27_3602_, v_j_3594_, v___y_3604_);
lean_dec(v_j_3594_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3605_);
v___x_3607_ = v___x_3598_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
else
{
lean_object* v_ks_3637_; lean_object* v_vs_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3656_; 
v_ks_3637_ = lean_ctor_get(v_x_3586_, 0);
v_vs_3638_ = lean_ctor_get(v_x_3586_, 1);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_x_3586_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3640_ = v_x_3586_;
v_isShared_3641_ = v_isSharedCheck_3656_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_vs_3638_);
lean_inc(v_ks_3637_);
lean_dec(v_x_3586_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3656_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_ks_3637_);
lean_ctor_set(v_reuseFailAlloc_3655_, 1, v_vs_3638_);
v___x_3643_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
lean_object* v_newNode_3644_; size_t v___x_3645_; uint8_t v___x_3646_; 
v_newNode_3644_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(v___x_3643_, v_x_3589_, v_x_3590_);
v___x_3645_ = ((size_t)7ULL);
v___x_3646_ = lean_usize_dec_le(v___x_3645_, v_x_3588_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3647_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3644_);
v___x_3648_ = lean_unsigned_to_nat(4u);
v___x_3649_ = lean_nat_dec_lt(v___x_3647_, v___x_3648_);
lean_dec(v___x_3647_);
if (v___x_3649_ == 0)
{
lean_object* v_ks_3650_; lean_object* v_vs_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v_ks_3650_ = lean_ctor_get(v_newNode_3644_, 0);
lean_inc_ref(v_ks_3650_);
v_vs_3651_ = lean_ctor_get(v_newNode_3644_, 1);
lean_inc_ref(v_vs_3651_);
lean_dec_ref(v_newNode_3644_);
v___x_3652_ = lean_unsigned_to_nat(0u);
v___x_3653_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0);
v___x_3654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_x_3588_, v_ks_3650_, v_vs_3651_, v___x_3652_, v___x_3653_);
lean_dec_ref(v_vs_3651_);
lean_dec_ref(v_ks_3650_);
return v___x_3654_;
}
else
{
return v_newNode_3644_;
}
}
else
{
return v_newNode_3644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(size_t v_depth_3657_, lean_object* v_keys_3658_, lean_object* v_vals_3659_, lean_object* v_i_3660_, lean_object* v_entries_3661_){
_start:
{
lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3662_ = lean_array_get_size(v_keys_3658_);
v___x_3663_ = lean_nat_dec_lt(v_i_3660_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_dec(v_i_3660_);
return v_entries_3661_;
}
else
{
lean_object* v_k_3664_; lean_object* v_v_3665_; uint64_t v___x_3666_; size_t v_h_3667_; size_t v___x_3668_; lean_object* v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; size_t v_h_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_k_3664_ = lean_array_fget_borrowed(v_keys_3658_, v_i_3660_);
v_v_3665_ = lean_array_fget_borrowed(v_vals_3659_, v_i_3660_);
v___x_3666_ = l_Lean_instHashableMVarId_hash(v_k_3664_);
v_h_3667_ = lean_uint64_to_usize(v___x_3666_);
v___x_3668_ = ((size_t)5ULL);
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = ((size_t)1ULL);
v___x_3671_ = lean_usize_sub(v_depth_3657_, v___x_3670_);
v___x_3672_ = lean_usize_mul(v___x_3668_, v___x_3671_);
v_h_3673_ = lean_usize_shift_right(v_h_3667_, v___x_3672_);
v___x_3674_ = lean_nat_add(v_i_3660_, v___x_3669_);
lean_dec(v_i_3660_);
lean_inc(v_v_3665_);
lean_inc(v_k_3664_);
v___x_3675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_entries_3661_, v_h_3673_, v_depth_3657_, v_k_3664_, v_v_3665_);
v_i_3660_ = v___x_3674_;
v_entries_3661_ = v___x_3675_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_3677_, lean_object* v_keys_3678_, lean_object* v_vals_3679_, lean_object* v_i_3680_, lean_object* v_entries_3681_){
_start:
{
size_t v_depth_boxed_3682_; lean_object* v_res_3683_; 
v_depth_boxed_3682_ = lean_unbox_usize(v_depth_3677_);
lean_dec(v_depth_3677_);
v_res_3683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_depth_boxed_3682_, v_keys_3678_, v_vals_3679_, v_i_3680_, v_entries_3681_);
lean_dec_ref(v_vals_3679_);
lean_dec_ref(v_keys_3678_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___boxed(lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_){
_start:
{
size_t v_x_5644__boxed_3689_; size_t v_x_5645__boxed_3690_; lean_object* v_res_3691_; 
v_x_5644__boxed_3689_ = lean_unbox_usize(v_x_3685_);
lean_dec(v_x_3685_);
v_x_5645__boxed_3690_ = lean_unbox_usize(v_x_3686_);
lean_dec(v_x_3686_);
v_res_3691_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3684_, v_x_5644__boxed_3689_, v_x_5645__boxed_3690_, v_x_3687_, v_x_3688_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
uint64_t v___x_3695_; size_t v___x_3696_; size_t v___x_3697_; lean_object* v___x_3698_; 
v___x_3695_ = l_Lean_instHashableMVarId_hash(v_x_3693_);
v___x_3696_ = lean_uint64_to_usize(v___x_3695_);
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3692_, v___x_3696_, v___x_3697_, v_x_3693_, v_x_3694_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(lean_object* v_mvarId_3699_, lean_object* v_val_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v___x_3703_; lean_object* v_mctx_3704_; lean_object* v_cache_3705_; lean_object* v_zetaDeltaFVarIds_3706_; lean_object* v_postponed_3707_; lean_object* v_diag_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3737_; 
v___x_3703_ = lean_st_ref_take(v___y_3701_);
v_mctx_3704_ = lean_ctor_get(v___x_3703_, 0);
v_cache_3705_ = lean_ctor_get(v___x_3703_, 1);
v_zetaDeltaFVarIds_3706_ = lean_ctor_get(v___x_3703_, 2);
v_postponed_3707_ = lean_ctor_get(v___x_3703_, 3);
v_diag_3708_ = lean_ctor_get(v___x_3703_, 4);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3710_ = v___x_3703_;
v_isShared_3711_ = v_isSharedCheck_3737_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_diag_3708_);
lean_inc(v_postponed_3707_);
lean_inc(v_zetaDeltaFVarIds_3706_);
lean_inc(v_cache_3705_);
lean_inc(v_mctx_3704_);
lean_dec(v___x_3703_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3737_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v_depth_3712_; lean_object* v_levelAssignDepth_3713_; lean_object* v_lmvarCounter_3714_; lean_object* v_mvarCounter_3715_; lean_object* v_lDecls_3716_; lean_object* v_decls_3717_; lean_object* v_userNames_3718_; lean_object* v_lAssignment_3719_; lean_object* v_eAssignment_3720_; lean_object* v_dAssignment_3721_; lean_object* v_instanceTypedMVars_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3736_; 
v_depth_3712_ = lean_ctor_get(v_mctx_3704_, 0);
v_levelAssignDepth_3713_ = lean_ctor_get(v_mctx_3704_, 1);
v_lmvarCounter_3714_ = lean_ctor_get(v_mctx_3704_, 2);
v_mvarCounter_3715_ = lean_ctor_get(v_mctx_3704_, 3);
v_lDecls_3716_ = lean_ctor_get(v_mctx_3704_, 4);
v_decls_3717_ = lean_ctor_get(v_mctx_3704_, 5);
v_userNames_3718_ = lean_ctor_get(v_mctx_3704_, 6);
v_lAssignment_3719_ = lean_ctor_get(v_mctx_3704_, 7);
v_eAssignment_3720_ = lean_ctor_get(v_mctx_3704_, 8);
v_dAssignment_3721_ = lean_ctor_get(v_mctx_3704_, 9);
v_instanceTypedMVars_3722_ = lean_ctor_get(v_mctx_3704_, 10);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_mctx_3704_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3724_ = v_mctx_3704_;
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_instanceTypedMVars_3722_);
lean_inc(v_dAssignment_3721_);
lean_inc(v_eAssignment_3720_);
lean_inc(v_lAssignment_3719_);
lean_inc(v_userNames_3718_);
lean_inc(v_decls_3717_);
lean_inc(v_lDecls_3716_);
lean_inc(v_mvarCounter_3715_);
lean_inc(v_lmvarCounter_3714_);
lean_inc(v_levelAssignDepth_3713_);
lean_inc(v_depth_3712_);
lean_dec(v_mctx_3704_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(v_eAssignment_3720_, v_mvarId_3699_, v_val_3700_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 8, v___x_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_depth_3712_);
lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_levelAssignDepth_3713_);
lean_ctor_set(v_reuseFailAlloc_3735_, 2, v_lmvarCounter_3714_);
lean_ctor_set(v_reuseFailAlloc_3735_, 3, v_mvarCounter_3715_);
lean_ctor_set(v_reuseFailAlloc_3735_, 4, v_lDecls_3716_);
lean_ctor_set(v_reuseFailAlloc_3735_, 5, v_decls_3717_);
lean_ctor_set(v_reuseFailAlloc_3735_, 6, v_userNames_3718_);
lean_ctor_set(v_reuseFailAlloc_3735_, 7, v_lAssignment_3719_);
lean_ctor_set(v_reuseFailAlloc_3735_, 8, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3735_, 9, v_dAssignment_3721_);
lean_ctor_set(v_reuseFailAlloc_3735_, 10, v_instanceTypedMVars_3722_);
v___x_3729_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 0, v___x_3729_);
v___x_3731_ = v___x_3710_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_cache_3705_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_zetaDeltaFVarIds_3706_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_postponed_3707_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_diag_3708_);
v___x_3731_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_st_ref_put(v___y_3701_, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3726_);
return v___x_3733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg___boxed(lean_object* v_mvarId_3738_, lean_object* v_val_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_mvarId_3738_, v_val_3739_, v___y_3740_);
lean_dec(v___y_3740_);
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(lean_object* v_motive_3743_, lean_object* v_ys_3744_, lean_object* v_e_3745_, lean_object* v___f_3746_, lean_object* v_cls_3747_, uint8_t v___x_3748_, lean_object* v_eqs_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3755_ = l_Lean_Expr_beta(v_motive_3743_, v_ys_3744_);
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
v___x_3757_ = 0;
v___x_3758_ = lean_box(0);
v___x_3759_ = l_Lean_Meta_mkFreshExprMVar(v___x_3756_, v___x_3757_, v___x_3758_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; size_t v_sz_3764_; size_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_a_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = l_Lean_Expr_mvarId_x21(v_a_3760_);
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3761_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v_sz_3764_ = lean_array_size(v_eqs_3749_);
v___x_3765_ = ((size_t)0ULL);
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(v_eqs_3749_, v_sz_3764_, v___x_3765_, v___x_3763_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v_fst_3768_; lean_object* v_snd_3769_; lean_object* v___x_3770_; lean_object* v___f_3771_; lean_object* v___x_3772_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v_fst_3768_ = lean_ctor_get(v_a_3767_, 0);
lean_inc_n(v_fst_3768_, 3);
v_snd_3769_ = lean_ctor_get(v_a_3767_, 1);
lean_inc(v_snd_3769_);
lean_dec(v_a_3767_);
v___x_3770_ = l_Lean_Meta_FVarSubst_apply(v_snd_3769_, v_e_3745_);
lean_inc_ref(v___x_3770_);
v___f_3771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed), 9, 4);
lean_closure_set(v___f_3771_, 0, v___f_3746_);
lean_closure_set(v___f_3771_, 1, v___x_3770_);
lean_closure_set(v___f_3771_, 2, v_fst_3768_);
lean_closure_set(v___f_3771_, 3, v_cls_3747_);
v___x_3772_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_fst_3768_, v___f_3771_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v_a_3775_; uint8_t v___x_3776_; uint8_t v___x_3777_; lean_object* v___x_3778_; 
lean_dec_ref_known(v___x_3772_, 1);
v___x_3773_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_fst_3768_, v___x_3770_, v___y_3751_);
lean_dec_ref(v___x_3773_);
v___x_3774_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_a_3760_, v___y_3751_);
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = 0;
v___x_3777_ = 1;
v___x_3778_ = l_Lean_Meta_mkLambdaFVars(v_eqs_3749_, v_a_3775_, v___x_3776_, v___x_3748_, v___x_3776_, v___x_3748_, v___x_3777_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
return v___x_3778_;
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v___x_3770_);
lean_dec(v_fst_3768_);
lean_dec(v_a_3760_);
v_a_3779_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3772_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3772_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v_a_3760_);
lean_dec(v_cls_3747_);
lean_dec_ref(v___f_3746_);
v_a_3787_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3766_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3766_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_dec(v_cls_3747_);
lean_dec_ref(v___f_3746_);
return v___x_3759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2___boxed(lean_object* v_motive_3795_, lean_object* v_ys_3796_, lean_object* v_e_3797_, lean_object* v___f_3798_, lean_object* v_cls_3799_, lean_object* v___x_3800_, lean_object* v_eqs_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v___x_5855__boxed_3807_; lean_object* v_res_3808_; 
v___x_5855__boxed_3807_ = lean_unbox(v___x_3800_);
v_res_3808_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(v_motive_3795_, v_ys_3796_, v_e_3797_, v___f_3798_, v_cls_3799_, v___x_5855__boxed_3807_, v_eqs_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
lean_dec_ref(v_eqs_3801_);
lean_dec_ref(v_e_3797_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
if (lean_obj_tag(v_a_3809_) == 0)
{
lean_object* v___x_3811_; 
v___x_3811_ = l_List_reverse___redArg(v_a_3810_);
return v___x_3811_;
}
else
{
lean_object* v_head_3812_; lean_object* v_tail_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3822_; 
v_head_3812_ = lean_ctor_get(v_a_3809_, 0);
v_tail_3813_ = lean_ctor_get(v_a_3809_, 1);
v_isSharedCheck_3822_ = !lean_is_exclusive(v_a_3809_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3815_ = v_a_3809_;
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_tail_3813_);
lean_inc(v_head_3812_);
lean_dec(v_a_3809_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3822_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3817_ = l_Lean_MessageData_ofExpr(v_head_3812_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 1, v_a_3810_);
lean_ctor_set(v___x_3815_, 0, v___x_3817_);
v___x_3819_ = v___x_3815_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3817_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_a_3810_);
v___x_3819_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
v_a_3809_ = v_tail_3813_;
v_a_3810_ = v___x_3819_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3827_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__2));
v___x_3828_ = lean_unsigned_to_nat(2u);
v___x_3829_ = lean_unsigned_to_nat(192u);
v___x_3830_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__1));
v___x_3831_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_3832_ = l_mkPanicMessageWithDecl(v___x_3831_, v___x_3830_, v___x_3829_, v___x_3828_, v___x_3827_);
return v___x_3832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3834_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__4));
v___x_3835_ = l_Lean_stringToMessageData(v___x_3834_);
return v___x_3835_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7(void){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3837_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__6));
v___x_3838_ = l_Lean_stringToMessageData(v___x_3837_);
return v___x_3838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9(void){
_start:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__8));
v___x_3841_ = l_Lean_stringToMessageData(v___x_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(lean_object* v_motive_3842_, lean_object* v_e_3843_, lean_object* v_xs_3844_, lean_object* v_ys_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_cls_3851_; lean_object* v___f_3852_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___x_3866_; lean_object* v_a_3867_; uint8_t v___x_3868_; 
v_cls_3851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___f_3852_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__0));
v___x_3866_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(v_cls_3851_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = lean_unbox(v_a_3867_);
lean_dec(v_a_3867_);
if (v___x_3868_ == 0)
{
v___y_3854_ = v_a_3846_;
v___y_3855_ = v_a_3847_;
v___y_3856_ = v_a_3848_;
v___y_3857_ = v_a_3849_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3869_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__5);
lean_inc_ref(v_e_3843_);
v___x_3870_ = l_Lean_MessageData_ofExpr(v_e_3843_);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__7);
v___x_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
lean_inc_ref(v_xs_3844_);
v___x_3874_ = lean_array_to_list(v_xs_3844_);
v___x_3875_ = lean_box(0);
v___x_3876_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(v___x_3874_, v___x_3875_);
v___x_3877_ = l_Lean_MessageData_ofList(v___x_3876_);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3873_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__9);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
lean_inc_ref(v_ys_3845_);
v___x_3881_ = lean_array_to_list(v_ys_3845_);
v___x_3882_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__6(v___x_3881_, v___x_3875_);
v___x_3883_ = l_Lean_MessageData_ofList(v___x_3882_);
v___x_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3880_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3851_, v___x_3884_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_dec_ref_known(v___x_3885_, 1);
v___y_3854_ = v_a_3846_;
v___y_3855_ = v_a_3847_;
v___y_3856_ = v_a_3848_;
v___y_3857_ = v_a_3849_;
goto v___jp_3853_;
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v_ys_3845_);
lean_dec_ref(v_xs_3844_);
lean_dec_ref(v_e_3843_);
lean_dec_ref(v_motive_3842_);
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
v___jp_3853_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v___x_3858_ = lean_array_get_size(v_xs_3844_);
v___x_3859_ = lean_array_get_size(v_ys_3845_);
v___x_3860_ = lean_nat_dec_eq(v___x_3858_, v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec_ref(v_ys_3845_);
lean_dec_ref(v_xs_3844_);
lean_dec_ref(v_e_3843_);
lean_dec_ref(v_motive_3842_);
v___x_3861_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___closed__3);
v___x_3862_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(v___x_3861_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3862_;
}
else
{
lean_object* v___x_3863_; lean_object* v___f_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_box(v___x_3860_);
lean_inc_ref(v_ys_3845_);
v___f_3864_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2___boxed), 12, 6);
lean_closure_set(v___f_3864_, 0, v_motive_3842_);
lean_closure_set(v___f_3864_, 1, v_ys_3845_);
lean_closure_set(v___f_3864_, 2, v_e_3843_);
lean_closure_set(v___f_3864_, 3, v___f_3852_);
lean_closure_set(v___f_3864_, 4, v_cls_3851_);
lean_closure_set(v___f_3864_, 5, v___x_3863_);
v___x_3865_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_3844_, v_ys_3845_, v___f_3864_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___boxed(lean_object* v_motive_3894_, lean_object* v_e_3895_, lean_object* v_xs_3896_, lean_object* v_ys_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(v_motive_3894_, v_e_3895_, v_xs_3896_, v_ys_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4(lean_object* v_mvarId_3904_, lean_object* v_val_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(v_mvarId_3904_, v_val_3905_, v___y_3907_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___boxed(lean_object* v_mvarId_3912_, lean_object* v_val_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4(v_mvarId_3912_, v_val_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4(lean_object* v_00_u03b2_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(v_x_3921_, v_x_3922_, v_x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(lean_object* v_00_u03b2_3925_, lean_object* v_x_3926_, size_t v_x_3927_, size_t v_x_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
lean_object* v___x_3931_; 
v___x_3931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3926_, v_x_3927_, v_x_3928_, v_x_3929_, v_x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3932_, lean_object* v_x_3933_, lean_object* v_x_3934_, lean_object* v_x_3935_, lean_object* v_x_3936_, lean_object* v_x_3937_){
_start:
{
size_t v_x_6164__boxed_3938_; size_t v_x_6165__boxed_3939_; lean_object* v_res_3940_; 
v_x_6164__boxed_3938_ = lean_unbox_usize(v_x_3934_);
lean_dec(v_x_3934_);
v_x_6165__boxed_3939_ = lean_unbox_usize(v_x_3935_);
lean_dec(v_x_3935_);
v_res_3940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(v_00_u03b2_3932_, v_x_3933_, v_x_6164__boxed_3938_, v_x_6165__boxed_3939_, v_x_3936_, v_x_3937_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8(lean_object* v_00_u03b2_3941_, lean_object* v_n_3942_, lean_object* v_k_3943_, lean_object* v_v_3944_){
_start:
{
lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(v_n_3942_, v_k_3943_, v_v_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9(lean_object* v_00_u03b2_3946_, size_t v_depth_3947_, lean_object* v_keys_3948_, lean_object* v_vals_3949_, lean_object* v_heq_3950_, lean_object* v_i_3951_, lean_object* v_entries_3952_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_depth_3947_, v_keys_3948_, v_vals_3949_, v_i_3951_, v_entries_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___boxed(lean_object* v_00_u03b2_3954_, lean_object* v_depth_3955_, lean_object* v_keys_3956_, lean_object* v_vals_3957_, lean_object* v_heq_3958_, lean_object* v_i_3959_, lean_object* v_entries_3960_){
_start:
{
size_t v_depth_boxed_3961_; lean_object* v_res_3962_; 
v_depth_boxed_3961_ = lean_unbox_usize(v_depth_3955_);
lean_dec(v_depth_3955_);
v_res_3962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9(v_00_u03b2_3954_, v_depth_boxed_3961_, v_keys_3956_, v_vals_3957_, v_heq_3958_, v_i_3959_, v_entries_3960_);
lean_dec_ref(v_vals_3957_);
lean_dec_ref(v_keys_3956_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_){
_start:
{
lean_object* v___x_3968_; 
v___x_3968_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(v_x_3964_, v_x_3965_, v_x_3966_, v_x_3967_);
return v___x_3968_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__2));
v___x_3974_ = l_Lean_stringToMessageData(v___x_3973_);
return v___x_3974_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__4));
v___x_3977_ = l_Lean_stringToMessageData(v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(lean_object* v_ctor_3978_, lean_object* v_as_3979_, size_t v_sz_3980_, size_t v_i_3981_, lean_object* v_b_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_a_3989_; uint8_t v___x_3993_; 
v___x_3993_ = lean_usize_dec_lt(v_i_3981_, v_sz_3980_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; 
lean_dec(v_ctor_3978_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v_b_3982_);
return v___x_3994_;
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; uint8_t v___x_3998_; 
v_a_3995_ = lean_array_uget_borrowed(v_as_3979_, v_i_3981_);
v___x_3996_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0));
v___x_3997_ = lean_unsigned_to_nat(3u);
v___x_3998_ = l_Lean_Expr_isAppOfArity(v_a_3995_, v___x_3996_, v___x_3997_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1));
v___x_4000_ = lean_unsigned_to_nat(4u);
v___x_4001_ = l_Lean_Expr_isAppOfArity(v_a_3995_, v___x_3999_, v___x_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4002_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__3);
lean_inc(v_a_3995_);
v___x_4003_ = l_Lean_MessageData_ofExpr(v_a_3995_);
v___x_4004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4002_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__5);
v___x_4006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4004_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
lean_inc(v_ctor_3978_);
v___x_4007_ = l_Lean_MessageData_ofName(v_ctor_3978_);
v___x_4008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4006_);
lean_ctor_set(v___x_4008_, 1, v___x_4007_);
v___x_4009_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_4008_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_dec_ref_known(v___x_4009_, 1);
v_a_3989_ = v_b_3982_;
goto v___jp_3988_;
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
lean_dec_ref(v_b_3982_);
lean_dec(v_ctor_3978_);
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4018_ = l_Lean_Expr_appFn_x21(v_a_3995_);
v___x_4019_ = l_Lean_Expr_appFn_x21(v___x_4018_);
lean_dec_ref(v___x_4018_);
v___x_4020_ = l_Lean_Expr_appArg_x21(v___x_4019_);
lean_dec_ref(v___x_4019_);
v___x_4021_ = l_Lean_Meta_mkHEqRefl(v___x_4020_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = l_Lean_Expr_app___override(v_b_3982_, v_a_4022_);
v_a_3989_ = v___x_4023_;
goto v___jp_3988_;
}
else
{
lean_dec_ref(v_b_3982_);
lean_dec(v_ctor_3978_);
return v___x_4021_;
}
}
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = l_Lean_Expr_appFn_x21(v_a_3995_);
v___x_4025_ = l_Lean_Expr_appArg_x21(v___x_4024_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = l_Lean_Meta_mkEqRefl(v___x_4025_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = l_Lean_Expr_app___override(v_b_3982_, v_a_4027_);
v_a_3989_ = v___x_4028_;
goto v___jp_3988_;
}
else
{
lean_dec_ref(v_b_3982_);
lean_dec(v_ctor_3978_);
return v___x_4026_;
}
}
}
v___jp_3988_:
{
size_t v___x_3990_; size_t v___x_3991_; 
v___x_3990_ = ((size_t)1ULL);
v___x_3991_ = lean_usize_add(v_i_3981_, v___x_3990_);
v_i_3981_ = v___x_3991_;
v_b_3982_ = v_a_3989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___boxed(lean_object* v_ctor_4029_, lean_object* v_as_4030_, lean_object* v_sz_4031_, lean_object* v_i_4032_, lean_object* v_b_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
size_t v_sz_boxed_4039_; size_t v_i_boxed_4040_; lean_object* v_res_4041_; 
v_sz_boxed_4039_ = lean_unbox_usize(v_sz_4031_);
lean_dec(v_sz_4031_);
v_i_boxed_4040_ = lean_unbox_usize(v_i_4032_);
lean_dec(v_i_4032_);
v_res_4041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(v_ctor_4029_, v_as_4030_, v_sz_boxed_4039_, v_i_boxed_4040_, v_b_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v_as_4030_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(lean_object* v___x_4042_, lean_object* v_head_4043_, lean_object* v_fs1_4044_, uint8_t v___x_4045_, uint8_t v___x_4046_, uint8_t v___x_4047_, lean_object* v_k_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = l_Lean_Expr_getNumHeadForalls(v___x_4042_);
v___x_4055_ = l_Lean_Meta_arrowDomainsN(v___x_4054_, v___x_4042_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; size_t v_sz_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v_sz_4057_ = lean_array_size(v_a_4056_);
v___x_4058_ = ((size_t)0ULL);
lean_inc_ref(v_k_4048_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0(v_head_4043_, v_a_4056_, v_sz_4057_, v___x_4058_, v_k_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v_a_4056_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = lean_mk_empty_array_with_capacity(v___x_4061_);
v___x_4063_ = lean_array_push(v___x_4062_, v_k_4048_);
v___x_4064_ = l_Array_append___redArg(v_fs1_4044_, v___x_4063_);
lean_dec_ref(v___x_4063_);
v___x_4065_ = l_Lean_Meta_mkLambdaFVars(v___x_4064_, v_a_4060_, v___x_4045_, v___x_4046_, v___x_4045_, v___x_4046_, v___x_4047_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec_ref(v___x_4064_);
return v___x_4065_;
}
else
{
lean_dec_ref(v_k_4048_);
lean_dec_ref(v_fs1_4044_);
return v___x_4059_;
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_dec_ref(v_k_4048_);
lean_dec_ref(v_fs1_4044_);
lean_dec(v_head_4043_);
v_a_4066_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4055_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4055_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0___boxed(lean_object* v___x_4074_, lean_object* v_head_4075_, lean_object* v_fs1_4076_, lean_object* v___x_4077_, lean_object* v___x_4078_, lean_object* v___x_4079_, lean_object* v_k_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v___x_11710__boxed_4086_; uint8_t v___x_11711__boxed_4087_; uint8_t v___x_11712__boxed_4088_; lean_object* v_res_4089_; 
v___x_11710__boxed_4086_ = lean_unbox(v___x_4077_);
v___x_11711__boxed_4087_ = lean_unbox(v___x_4078_);
v___x_11712__boxed_4088_ = lean_unbox(v___x_4079_);
v_res_4089_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(v___x_4074_, v_head_4075_, v_fs1_4076_, v___x_11710__boxed_4086_, v___x_11711__boxed_4087_, v___x_11712__boxed_4088_, v_k_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(lean_object* v_head_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, uint8_t v___x_4096_, uint8_t v___x_4097_, uint8_t v___x_4098_, lean_object* v_fs1_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; 
lean_inc(v_head_4093_);
v___x_4106_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_head_4093_, v___x_4094_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___f_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
lean_inc_ref(v___x_4095_);
v___x_4108_ = l_Array_append___redArg(v___x_4095_, v_fs1_4099_);
v___x_4109_ = l_Array_append___redArg(v___x_4108_, v___x_4095_);
lean_dec_ref(v___x_4095_);
v___x_4110_ = l_Array_append___redArg(v___x_4109_, v_fs1_4099_);
v___x_4111_ = l_Lean_Expr_beta(v_a_4107_, v___x_4110_);
v___x_4112_ = lean_box(v___x_4096_);
v___x_4113_ = lean_box(v___x_4097_);
v___x_4114_ = lean_box(v___x_4098_);
lean_inc_ref(v___x_4111_);
v___f_4115_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0___boxed), 12, 6);
lean_closure_set(v___f_4115_, 0, v___x_4111_);
lean_closure_set(v___f_4115_, 1, v_head_4093_);
lean_closure_set(v___f_4115_, 2, v_fs1_4099_);
lean_closure_set(v___f_4115_, 3, v___x_4112_);
lean_closure_set(v___f_4115_, 4, v___x_4113_);
lean_closure_set(v___f_4115_, 5, v___x_4114_);
v___x_4116_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1));
v___x_4117_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_4116_, v___x_4111_, v___f_4115_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4117_;
}
else
{
lean_dec_ref(v_fs1_4099_);
lean_dec_ref(v___x_4095_);
lean_dec(v_head_4093_);
return v___x_4106_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___boxed(lean_object* v_head_4118_, lean_object* v___x_4119_, lean_object* v___x_4120_, lean_object* v___x_4121_, lean_object* v___x_4122_, lean_object* v___x_4123_, lean_object* v_fs1_4124_, lean_object* v_x_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
uint8_t v___x_11786__boxed_4131_; uint8_t v___x_11787__boxed_4132_; uint8_t v___x_11788__boxed_4133_; lean_object* v_res_4134_; 
v___x_11786__boxed_4131_ = lean_unbox(v___x_4121_);
v___x_11787__boxed_4132_ = lean_unbox(v___x_4122_);
v___x_11788__boxed_4133_ = lean_unbox(v___x_4123_);
v_res_4134_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(v_head_4118_, v___x_4119_, v___x_4120_, v___x_11786__boxed_4131_, v___x_11787__boxed_4132_, v___x_11788__boxed_4133_, v_fs1_4124_, v_x_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec_ref(v_x_4125_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(lean_object* v___x_4135_, lean_object* v___x_4136_, lean_object* v_tail_4137_, lean_object* v_x_4138_, lean_object* v_x_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
if (lean_obj_tag(v_x_4138_) == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec(v_tail_4137_);
lean_dec_ref(v___x_4136_);
lean_dec_ref(v___x_4135_);
v___x_4145_ = l_List_reverse___redArg(v_x_4139_);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
else
{
lean_object* v_head_4147_; lean_object* v_tail_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4179_; 
v_head_4147_ = lean_ctor_get(v_x_4138_, 0);
v_tail_4148_ = lean_ctor_get(v_x_4138_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_x_4138_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4150_ = v_x_4138_;
v_isShared_4151_ = v_isSharedCheck_4179_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_tail_4148_);
lean_inc(v_head_4147_);
lean_dec(v_x_4138_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4179_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
lean_object* v___y_4153_; uint8_t v___x_4167_; uint8_t v___x_4168_; uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4167_ = 0;
v___x_4168_ = 1;
v___x_4169_ = 1;
v___x_4170_ = lean_box(v___x_4167_);
v___x_4171_ = lean_box(v___x_4168_);
v___x_4172_ = lean_box(v___x_4169_);
lean_inc_ref(v___x_4136_);
lean_inc_ref(v___x_4135_);
lean_inc(v_head_4147_);
v___f_4173_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___boxed), 13, 6);
lean_closure_set(v___f_4173_, 0, v_head_4147_);
lean_closure_set(v___f_4173_, 1, v___x_4135_);
lean_closure_set(v___f_4173_, 2, v___x_4136_);
lean_closure_set(v___f_4173_, 3, v___x_4170_);
lean_closure_set(v___f_4173_, 4, v___x_4171_);
lean_closure_set(v___f_4173_, 5, v___x_4172_);
lean_inc(v_tail_4137_);
v___x_4174_ = l_Lean_mkConst(v_head_4147_, v_tail_4137_);
v___x_4175_ = l_Lean_mkAppN(v___x_4174_, v___x_4136_);
lean_inc(v___y_4143_);
lean_inc_ref(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc_ref(v___y_4140_);
v___x_4176_ = lean_infer_type(v___x_4175_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref_known(v___x_4176_, 1);
v___x_4178_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v_a_4177_, v___f_4173_, v___x_4167_, v___x_4167_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
v___y_4153_ = v___x_4178_;
goto v___jp_4152_;
}
else
{
lean_dec_ref(v___f_4173_);
v___y_4153_ = v___x_4176_;
goto v___jp_4152_;
}
v___jp_4152_:
{
if (lean_obj_tag(v___y_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4156_; 
v_a_4154_ = lean_ctor_get(v___y_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___y_4153_, 1);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 1, v_x_4139_);
lean_ctor_set(v___x_4150_, 0, v_a_4154_);
v___x_4156_ = v___x_4150_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4154_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_x_4139_);
v___x_4156_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
v_x_4138_ = v_tail_4148_;
v_x_4139_ = v___x_4156_;
goto _start;
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_del_object(v___x_4150_);
lean_dec(v_tail_4148_);
lean_dec(v_x_4139_);
lean_dec(v_tail_4137_);
lean_dec_ref(v___x_4136_);
lean_dec_ref(v___x_4135_);
v_a_4159_ = lean_ctor_get(v___y_4153_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___y_4153_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___y_4153_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___y_4153_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___boxed(lean_object* v___x_4180_, lean_object* v___x_4181_, lean_object* v_tail_4182_, lean_object* v_x_4183_, lean_object* v_x_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(v___x_4180_, v___x_4181_, v_tail_4182_, v_x_4183_, v_x_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(lean_object* v___x_4191_, lean_object* v___x_4192_, uint8_t v___x_4193_, uint8_t v___x_4194_, uint8_t v___x_4195_, lean_object* v___x_4196_, lean_object* v___x_4197_, lean_object* v_tail_4198_, lean_object* v_ctors_4199_, lean_object* v___x_4200_, lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v___x_4203_, lean_object* v_xs2_4204_, lean_object* v___x_4205_, lean_object* v_xs1_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Lean_Meta_mkLambdaFVars(v___x_4191_, v___x_4192_, v___x_4193_, v___x_4194_, v___x_4193_, v___x_4194_, v___x_4195_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = lean_box(0);
lean_inc_ref(v___x_4197_);
v___x_4215_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1(v___x_4196_, v___x_4197_, v_tail_4198_, v_ctors_4199_, v___x_4214_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = l_Lean_mkConst(v___x_4200_, v___x_4201_);
v___x_4218_ = lean_array_push(v___x_4202_, v_a_4213_);
v___x_4219_ = l_Array_append___redArg(v___x_4197_, v___x_4218_);
lean_dec_ref(v___x_4218_);
v___x_4220_ = l_Array_append___redArg(v___x_4219_, v___x_4191_);
v___x_4221_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_4220_, v_a_4216_);
v___x_4222_ = l_Lean_mkAppN(v___x_4217_, v___x_4221_);
lean_dec_ref(v___x_4221_);
v___x_4223_ = l_Array_append___redArg(v___x_4203_, v_xs2_4204_);
v___x_4224_ = l_Lean_mkAppN(v___x_4205_, v___x_4223_);
v___x_4225_ = l_Lean_Meta_mkLambdaFVars(v_xs2_4204_, v___x_4224_, v___x_4193_, v___x_4194_, v___x_4193_, v___x_4194_, v___x_4195_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope(v_a_4226_, v___x_4222_, v_xs1_4206_, v_xs2_4204_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = l_Lean_Meta_mkLambdaFVars(v___x_4223_, v_a_4228_, v___x_4193_, v___x_4194_, v___x_4193_, v___x_4194_, v___x_4195_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec_ref(v___x_4223_);
return v___x_4229_;
}
else
{
lean_dec_ref(v___x_4223_);
return v___x_4227_;
}
}
else
{
lean_dec_ref(v___x_4223_);
lean_dec_ref(v___x_4222_);
lean_dec_ref(v_xs1_4206_);
lean_dec_ref(v_xs2_4204_);
return v___x_4225_;
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_a_4213_);
lean_dec_ref(v_xs1_4206_);
lean_dec_ref(v___x_4205_);
lean_dec_ref(v_xs2_4204_);
lean_dec_ref(v___x_4203_);
lean_dec_ref(v___x_4202_);
lean_dec(v___x_4201_);
lean_dec(v___x_4200_);
lean_dec_ref(v___x_4197_);
v_a_4230_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4215_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4215_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_dec_ref(v_xs1_4206_);
lean_dec_ref(v___x_4205_);
lean_dec_ref(v_xs2_4204_);
lean_dec_ref(v___x_4203_);
lean_dec_ref(v___x_4202_);
lean_dec(v___x_4201_);
lean_dec(v___x_4200_);
lean_dec(v_ctors_4199_);
lean_dec(v_tail_4198_);
lean_dec_ref(v___x_4197_);
lean_dec_ref(v___x_4196_);
return v___x_4212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0___boxed(lean_object** _args){
lean_object* v___x_4238_ = _args[0];
lean_object* v___x_4239_ = _args[1];
lean_object* v___x_4240_ = _args[2];
lean_object* v___x_4241_ = _args[3];
lean_object* v___x_4242_ = _args[4];
lean_object* v___x_4243_ = _args[5];
lean_object* v___x_4244_ = _args[6];
lean_object* v_tail_4245_ = _args[7];
lean_object* v_ctors_4246_ = _args[8];
lean_object* v___x_4247_ = _args[9];
lean_object* v___x_4248_ = _args[10];
lean_object* v___x_4249_ = _args[11];
lean_object* v___x_4250_ = _args[12];
lean_object* v_xs2_4251_ = _args[13];
lean_object* v___x_4252_ = _args[14];
lean_object* v_xs1_4253_ = _args[15];
lean_object* v___y_4254_ = _args[16];
lean_object* v___y_4255_ = _args[17];
lean_object* v___y_4256_ = _args[18];
lean_object* v___y_4257_ = _args[19];
lean_object* v___y_4258_ = _args[20];
_start:
{
uint8_t v___x_11950__boxed_4259_; uint8_t v___x_11951__boxed_4260_; uint8_t v___x_11952__boxed_4261_; lean_object* v_res_4262_; 
v___x_11950__boxed_4259_ = lean_unbox(v___x_4240_);
v___x_11951__boxed_4260_ = lean_unbox(v___x_4241_);
v___x_11952__boxed_4261_ = lean_unbox(v___x_4242_);
v_res_4262_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(v___x_4238_, v___x_4239_, v___x_11950__boxed_4259_, v___x_11951__boxed_4260_, v___x_11952__boxed_4261_, v___x_4243_, v___x_4244_, v_tail_4245_, v_ctors_4246_, v___x_4247_, v___x_4248_, v___x_4249_, v___x_4250_, v_xs2_4251_, v___x_4252_, v_xs1_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec_ref(v___x_4238_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(lean_object* v_bs_4263_, lean_object* v_k_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v___x_4270_; 
v___x_4270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_4263_, v_k_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
v_a_4279_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4270_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4270_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg___boxed(lean_object* v_bs_4287_, lean_object* v_k_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v_bs_4287_, v_k_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec_ref(v_bs_4287_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(size_t v_sz_4295_, size_t v_i_4296_, lean_object* v_bs_4297_){
_start:
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
if (v___x_4298_ == 0)
{
return v_bs_4297_;
}
else
{
lean_object* v_v_4299_; lean_object* v___x_4300_; lean_object* v_bs_x27_4301_; lean_object* v___x_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; size_t v___x_4306_; size_t v___x_4307_; lean_object* v___x_4308_; 
v_v_4299_ = lean_array_uget(v_bs_4297_, v_i_4296_);
v___x_4300_ = lean_unsigned_to_nat(0u);
v_bs_x27_4301_ = lean_array_uset(v_bs_4297_, v_i_4296_, v___x_4300_);
v___x_4302_ = l_Lean_Expr_fvarId_x21(v_v_4299_);
lean_dec(v_v_4299_);
v___x_4303_ = 1;
v___x_4304_ = lean_box(v___x_4303_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4302_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = ((size_t)1ULL);
v___x_4307_ = lean_usize_add(v_i_4296_, v___x_4306_);
v___x_4308_ = lean_array_uset(v_bs_x27_4301_, v_i_4296_, v___x_4305_);
v_i_4296_ = v___x_4307_;
v_bs_4297_ = v___x_4308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2___boxed(lean_object* v_sz_4310_, lean_object* v_i_4311_, lean_object* v_bs_4312_){
_start:
{
size_t v_sz_boxed_4313_; size_t v_i_boxed_4314_; lean_object* v_res_4315_; 
v_sz_boxed_4313_ = lean_unbox_usize(v_sz_4310_);
lean_dec(v_sz_4310_);
v_i_boxed_4314_ = lean_unbox_usize(v_i_4311_);
lean_dec(v_i_4311_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(v_sz_boxed_4313_, v_i_boxed_4314_, v_bs_4312_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(lean_object* v_bs_4316_, lean_object* v_k_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
size_t v_sz_4323_; size_t v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v_sz_4323_ = lean_array_size(v_bs_4316_);
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__2(v_sz_4323_, v___x_4324_, v_bs_4316_);
v___x_4326_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v___x_4325_, v_k_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec_ref(v___x_4325_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg___boxed(lean_object* v_bs_4327_, lean_object* v_k_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v_bs_4327_, v_k_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1(lean_object* v_xs1_4335_, lean_object* v___x_4336_, lean_object* v___x_4337_, lean_object* v_numParams_4338_, lean_object* v___x_4339_, lean_object* v___x_4340_, lean_object* v_tail_4341_, lean_object* v_ctors_4342_, lean_object* v___x_4343_, lean_object* v___x_4344_, lean_object* v_xs2_4345_, lean_object* v_x_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; uint8_t v___x_4365_; uint8_t v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; 
lean_inc_ref_n(v_xs1_4335_, 3);
v___x_4352_ = l_Array_append___redArg(v_xs1_4335_, v_xs2_4345_);
lean_inc_ref_n(v___x_4336_, 2);
v___x_4353_ = lean_array_push(v___x_4352_, v___x_4336_);
lean_inc(v_numParams_4338_);
v___x_4354_ = l_Array_toSubarray___redArg(v_xs1_4335_, v___x_4337_, v_numParams_4338_);
v___x_4355_ = l_Subarray_copy___redArg(v___x_4354_);
v___x_4356_ = lean_array_get_size(v_xs1_4335_);
v___x_4357_ = l_Array_toSubarray___redArg(v_xs1_4335_, v_numParams_4338_, v___x_4356_);
v___x_4358_ = l_Subarray_copy___redArg(v___x_4357_);
v___x_4359_ = lean_mk_empty_array_with_capacity(v___x_4339_);
lean_inc_ref(v___x_4359_);
v___x_4360_ = lean_array_push(v___x_4359_, v___x_4336_);
v___x_4361_ = l_Array_append___redArg(v___x_4360_, v_xs1_4335_);
lean_inc_ref(v___x_4361_);
v___x_4362_ = l_Array_append___redArg(v___x_4361_, v_xs1_4335_);
lean_inc_ref(v___x_4340_);
v___x_4363_ = l_Lean_mkAppN(v___x_4340_, v___x_4362_);
lean_dec_ref(v___x_4362_);
v___x_4364_ = 0;
v___x_4365_ = 1;
v___x_4366_ = 1;
v___x_4367_ = lean_box(v___x_4364_);
v___x_4368_ = lean_box(v___x_4365_);
v___x_4369_ = lean_box(v___x_4366_);
v___f_4370_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0___boxed), 21, 16);
lean_closure_set(v___f_4370_, 0, v___x_4358_);
lean_closure_set(v___f_4370_, 1, v___x_4363_);
lean_closure_set(v___f_4370_, 2, v___x_4367_);
lean_closure_set(v___f_4370_, 3, v___x_4368_);
lean_closure_set(v___f_4370_, 4, v___x_4369_);
lean_closure_set(v___f_4370_, 5, v___x_4336_);
lean_closure_set(v___f_4370_, 6, v___x_4355_);
lean_closure_set(v___f_4370_, 7, v_tail_4341_);
lean_closure_set(v___f_4370_, 8, v_ctors_4342_);
lean_closure_set(v___f_4370_, 9, v___x_4343_);
lean_closure_set(v___f_4370_, 10, v___x_4344_);
lean_closure_set(v___f_4370_, 11, v___x_4359_);
lean_closure_set(v___f_4370_, 12, v___x_4361_);
lean_closure_set(v___f_4370_, 13, v_xs2_4345_);
lean_closure_set(v___f_4370_, 14, v___x_4340_);
lean_closure_set(v___f_4370_, 15, v_xs1_4335_);
v___x_4371_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v___x_4353_, v___f_4370_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1___boxed(lean_object** _args){
lean_object* v_xs1_4372_ = _args[0];
lean_object* v___x_4373_ = _args[1];
lean_object* v___x_4374_ = _args[2];
lean_object* v_numParams_4375_ = _args[3];
lean_object* v___x_4376_ = _args[4];
lean_object* v___x_4377_ = _args[5];
lean_object* v_tail_4378_ = _args[6];
lean_object* v_ctors_4379_ = _args[7];
lean_object* v___x_4380_ = _args[8];
lean_object* v___x_4381_ = _args[9];
lean_object* v_xs2_4382_ = _args[10];
lean_object* v_x_4383_ = _args[11];
lean_object* v___y_4384_ = _args[12];
lean_object* v___y_4385_ = _args[13];
lean_object* v___y_4386_ = _args[14];
lean_object* v___y_4387_ = _args[15];
lean_object* v___y_4388_ = _args[16];
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1(v_xs1_4372_, v___x_4373_, v___x_4374_, v_numParams_4375_, v___x_4376_, v___x_4377_, v_tail_4378_, v_ctors_4379_, v___x_4380_, v___x_4381_, v_xs2_4382_, v_x_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec_ref(v_x_4383_);
lean_dec(v___x_4376_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2(lean_object* v___x_4390_, lean_object* v___x_4391_, lean_object* v_numParams_4392_, lean_object* v___x_4393_, lean_object* v___x_4394_, lean_object* v_tail_4395_, lean_object* v_ctors_4396_, lean_object* v___x_4397_, lean_object* v___x_4398_, lean_object* v___x_4399_, lean_object* v_xs1_4400_, lean_object* v_t_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___f_4407_; uint8_t v___x_4408_; lean_object* v___x_4409_; 
v___f_4407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__1___boxed), 17, 10);
lean_closure_set(v___f_4407_, 0, v_xs1_4400_);
lean_closure_set(v___f_4407_, 1, v___x_4390_);
lean_closure_set(v___f_4407_, 2, v___x_4391_);
lean_closure_set(v___f_4407_, 3, v_numParams_4392_);
lean_closure_set(v___f_4407_, 4, v___x_4393_);
lean_closure_set(v___f_4407_, 5, v___x_4394_);
lean_closure_set(v___f_4407_, 6, v_tail_4395_);
lean_closure_set(v___f_4407_, 7, v_ctors_4396_);
lean_closure_set(v___f_4407_, 8, v___x_4397_);
lean_closure_set(v___f_4407_, 9, v___x_4398_);
v___x_4408_ = 0;
v___x_4409_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_4401_, v___x_4399_, v___f_4407_, v___x_4408_, v___x_4408_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2___boxed(lean_object** _args){
lean_object* v___x_4410_ = _args[0];
lean_object* v___x_4411_ = _args[1];
lean_object* v_numParams_4412_ = _args[2];
lean_object* v___x_4413_ = _args[3];
lean_object* v___x_4414_ = _args[4];
lean_object* v_tail_4415_ = _args[5];
lean_object* v_ctors_4416_ = _args[6];
lean_object* v___x_4417_ = _args[7];
lean_object* v___x_4418_ = _args[8];
lean_object* v___x_4419_ = _args[9];
lean_object* v_xs1_4420_ = _args[10];
lean_object* v_t_4421_ = _args[11];
lean_object* v___y_4422_ = _args[12];
lean_object* v___y_4423_ = _args[13];
lean_object* v___y_4424_ = _args[14];
lean_object* v___y_4425_ = _args[15];
lean_object* v___y_4426_ = _args[16];
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2(v___x_4410_, v___x_4411_, v_numParams_4412_, v___x_4413_, v___x_4414_, v_tail_4415_, v_ctors_4416_, v___x_4417_, v___x_4418_, v___x_4419_, v_xs1_4420_, v_t_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3(lean_object* v_val_4428_, lean_object* v___x_4429_, lean_object* v___x_4430_, lean_object* v___x_4431_, lean_object* v_tail_4432_, lean_object* v___x_4433_, lean_object* v___x_4434_, lean_object* v_xs_4435_, lean_object* v_t_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_numParams_4442_; lean_object* v_numIndices_4443_; lean_object* v_ctors_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___f_4450_; uint8_t v___x_4451_; lean_object* v___x_4452_; 
v_numParams_4442_ = lean_ctor_get(v_val_4428_, 1);
lean_inc(v_numParams_4442_);
v_numIndices_4443_ = lean_ctor_get(v_val_4428_, 2);
lean_inc(v_numIndices_4443_);
v_ctors_4444_ = lean_ctor_get(v_val_4428_, 4);
lean_inc(v_ctors_4444_);
lean_dec_ref(v_val_4428_);
v___x_4445_ = lean_unsigned_to_nat(0u);
v___x_4446_ = lean_array_get_borrowed(v___x_4429_, v_xs_4435_, v___x_4445_);
v___x_4447_ = lean_nat_add(v_numParams_4442_, v_numIndices_4443_);
lean_dec(v_numIndices_4443_);
v___x_4448_ = lean_nat_add(v___x_4447_, v___x_4430_);
lean_dec(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4448_);
lean_inc_ref(v___x_4449_);
lean_inc(v___x_4446_);
v___f_4450_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__2___boxed), 17, 10);
lean_closure_set(v___f_4450_, 0, v___x_4446_);
lean_closure_set(v___f_4450_, 1, v___x_4445_);
lean_closure_set(v___f_4450_, 2, v_numParams_4442_);
lean_closure_set(v___f_4450_, 3, v___x_4430_);
lean_closure_set(v___f_4450_, 4, v___x_4431_);
lean_closure_set(v___f_4450_, 5, v_tail_4432_);
lean_closure_set(v___f_4450_, 6, v_ctors_4444_);
lean_closure_set(v___f_4450_, 7, v___x_4433_);
lean_closure_set(v___f_4450_, 8, v___x_4434_);
lean_closure_set(v___f_4450_, 9, v___x_4449_);
v___x_4451_ = 0;
v___x_4452_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_4436_, v___x_4449_, v___f_4450_, v___x_4451_, v___x_4451_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3___boxed(lean_object* v_val_4453_, lean_object* v___x_4454_, lean_object* v___x_4455_, lean_object* v___x_4456_, lean_object* v_tail_4457_, lean_object* v___x_4458_, lean_object* v___x_4459_, lean_object* v_xs_4460_, lean_object* v_t_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3(v_val_4453_, v___x_4454_, v___x_4455_, v___x_4456_, v_tail_4457_, v___x_4458_, v___x_4459_, v_xs_4460_, v_t_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec_ref(v_xs_4460_);
lean_dec_ref(v___x_4454_);
return v_res_4467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_4472_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
v___x_4473_ = l_Lean_Name_append(v___x_4472_, v___x_4471_);
return v___x_4473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__3));
v___x_4476_ = l_Lean_stringToMessageData(v___x_4475_);
return v___x_4476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6(void){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v___x_4478_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4));
v___x_4479_ = lean_unsigned_to_nat(58u);
v___x_4480_ = lean_unsigned_to_nat(216u);
v___x_4481_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5));
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_4483_ = l_mkPanicMessageWithDecl(v___x_4482_, v___x_4481_, v___x_4480_, v___x_4479_, v___x_4478_);
return v___x_4483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7(void){
_start:
{
lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4484_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_4485_ = lean_unsigned_to_nat(60u);
v___x_4486_ = lean_unsigned_to_nat(213u);
v___x_4487_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__5));
v___x_4488_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_4489_ = l_mkPanicMessageWithDecl(v___x_4488_, v___x_4487_, v___x_4486_, v___x_4485_, v___x_4484_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(lean_object* v_indName_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v_declName_4498_; lean_object* v_noConfusionTypeName_4499_; lean_object* v___x_4500_; 
v___x_4496_ = l_Lean_instInhabitedExpr;
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
lean_inc_n(v_indName_4490_, 3);
v_declName_4498_ = l_Lean_Name_str___override(v_indName_4490_, v___x_4497_);
v_noConfusionTypeName_4499_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(v_indName_4490_);
v___x_4500_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_indName_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
if (lean_obj_tag(v_a_4501_) == 5)
{
lean_object* v_val_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; 
v_val_4502_ = lean_ctor_get(v_a_4501_, 0);
lean_inc_ref(v_val_4502_);
lean_dec_ref_known(v_a_4501_, 1);
v___x_4503_ = l_Lean_mkCasesOnName(v_indName_4490_);
lean_inc(v___x_4503_);
v___x_4504_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v___x_4503_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
if (lean_obj_tag(v___x_4504_) == 0)
{
lean_object* v_a_4505_; lean_object* v_levelParams_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4673_; 
v_a_4505_ = lean_ctor_get(v___x_4504_, 0);
lean_inc(v_a_4505_);
lean_dec_ref_known(v___x_4504_, 1);
v_levelParams_4506_ = lean_ctor_get(v_a_4505_, 1);
v_isSharedCheck_4673_ = !lean_is_exclusive(v_a_4505_);
if (v_isSharedCheck_4673_ == 0)
{
lean_object* v_unused_4674_; lean_object* v_unused_4675_; 
v_unused_4674_ = lean_ctor_get(v_a_4505_, 2);
lean_dec(v_unused_4674_);
v_unused_4675_ = lean_ctor_get(v_a_4505_, 0);
lean_dec(v_unused_4675_);
v___x_4508_ = v_a_4505_;
v_isShared_4509_ = v_isSharedCheck_4673_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_levelParams_4506_);
lean_dec(v_a_4505_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4673_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = lean_box(0);
lean_inc(v_levelParams_4506_);
v___x_4511_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_4506_, v___x_4510_);
if (lean_obj_tag(v___x_4511_) == 1)
{
lean_object* v_tail_4512_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v_toCold_4660_; lean_object* v_options_4661_; uint8_t v_hasTrace_4662_; 
v_tail_4512_ = lean_ctor_get(v___x_4511_, 1);
lean_inc(v_tail_4512_);
v_toCold_4660_ = lean_ctor_get(v_a_4493_, 0);
v_options_4661_ = lean_ctor_get(v_toCold_4660_, 2);
v_hasTrace_4662_ = lean_ctor_get_uint8(v_options_4661_, sizeof(void*)*1);
if (v_hasTrace_4662_ == 0)
{
v___y_4514_ = v_a_4491_;
v___y_4515_ = v_a_4492_;
v___y_4516_ = v_a_4493_;
v___y_4517_ = v_a_4494_;
goto v___jp_4513_;
}
else
{
lean_object* v_inheritedTraceOptions_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; uint8_t v___x_4666_; 
v_inheritedTraceOptions_4663_ = lean_ctor_get(v_toCold_4660_, 11);
v___x_4664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_4665_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2);
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4663_, v_options_4661_, v___x_4665_);
if (v___x_4666_ == 0)
{
v___y_4514_ = v_a_4491_;
v___y_4515_ = v_a_4492_;
v___y_4516_ = v_a_4493_;
v___y_4517_ = v_a_4494_;
goto v___jp_4513_;
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v___x_4667_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__4);
lean_inc(v_declName_4498_);
v___x_4668_ = l_Lean_MessageData_ofName(v_declName_4498_);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v___x_4664_, v___x_4669_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_dec_ref_known(v___x_4670_, 1);
v___y_4514_ = v_a_4491_;
v___y_4515_ = v_a_4492_;
v___y_4516_ = v_a_4493_;
v___y_4517_ = v_a_4494_;
goto v___jp_4513_;
}
else
{
lean_dec(v_tail_4512_);
lean_dec_ref_known(v___x_4511_, 2);
lean_del_object(v___x_4508_);
lean_dec(v_levelParams_4506_);
lean_dec(v___x_4503_);
lean_dec_ref(v_val_4502_);
lean_dec(v_noConfusionTypeName_4499_);
lean_dec(v_declName_4498_);
return v___x_4670_;
}
}
}
v___jp_4513_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; 
lean_inc_ref(v___x_4511_);
v___x_4518_ = l_Lean_mkConst(v_noConfusionTypeName_4499_, v___x_4511_);
lean_inc(v___y_4517_);
lean_inc_ref(v___y_4516_);
lean_inc(v___y_4515_);
lean_inc_ref(v___y_4514_);
lean_inc_ref(v___x_4518_);
v___x_4519_ = lean_infer_type(v___x_4518_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4521_; lean_object* v___f_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; lean_object* v___x_4525_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v___x_4521_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_val_4502_);
v___f_4522_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__3___boxed), 14, 7);
lean_closure_set(v___f_4522_, 0, v_val_4502_);
lean_closure_set(v___f_4522_, 1, v___x_4496_);
lean_closure_set(v___f_4522_, 2, v___x_4521_);
lean_closure_set(v___f_4522_, 3, v___x_4518_);
lean_closure_set(v___f_4522_, 4, v_tail_4512_);
lean_closure_set(v___f_4522_, 5, v___x_4503_);
lean_closure_set(v___f_4522_, 6, v___x_4511_);
v___x_4523_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__1));
v___x_4524_ = 0;
v___x_4525_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_4520_, v___x_4523_, v___f_4522_, v___x_4524_, v___x_4524_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4527_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc_n(v_a_4526_, 2);
lean_dec_ref_known(v___x_4525_, 1);
lean_inc(v___y_4517_);
lean_inc_ref(v___y_4516_);
lean_inc(v___y_4515_);
lean_inc_ref(v___y_4514_);
v___x_4527_ = lean_infer_type(v_a_4526_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4635_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
v___x_4529_ = lean_box(1);
lean_inc(v_declName_4498_);
v___x_4530_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_declName_4498_, v_levelParams_4506_, v_a_4528_, v_a_4526_, v___x_4529_, v___y_4517_);
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4533_ = v___x_4530_;
v_isShared_4534_ = v_isSharedCheck_4635_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4530_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4635_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set_tag(v___x_4533_, 1);
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_addDecl(v___x_4536_, v___x_4524_, v___y_4516_, v___y_4517_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v___x_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4632_; 
lean_dec_ref_known(v___x_4537_, 1);
lean_inc(v_declName_4498_);
v___x_4538_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_4498_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4632_ == 0)
{
lean_object* v_unused_4633_; 
v_unused_4633_ = lean_ctor_get(v___x_4538_, 0);
lean_dec(v_unused_4633_);
v___x_4540_ = v___x_4538_;
v_isShared_4541_ = v_isSharedCheck_4632_;
goto v_resetjp_4539_;
}
else
{
lean_dec(v___x_4538_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4632_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v_numParams_4542_; lean_object* v_numIndices_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v_env_4558_; lean_object* v_nextMacroScope_4559_; lean_object* v_ngen_4560_; lean_object* v_auxDeclNGen_4561_; lean_object* v_traceState_4562_; lean_object* v_messages_4563_; lean_object* v_infoState_4564_; lean_object* v_snapshotTasks_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4630_; 
v_numParams_4542_ = lean_ctor_get(v_val_4502_, 1);
lean_inc(v_numParams_4542_);
v_numIndices_4543_ = lean_ctor_get(v_val_4502_, 2);
lean_inc(v_numIndices_4543_);
lean_dec_ref(v_val_4502_);
v___x_4544_ = lean_unsigned_to_nat(3u);
v___x_4545_ = lean_nat_add(v_numParams_4542_, v_numIndices_4543_);
v___x_4546_ = lean_nat_add(v___x_4545_, v___x_4521_);
lean_dec(v___x_4545_);
v___x_4547_ = lean_nat_mul(v___x_4544_, v___x_4546_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_nat_add(v___x_4521_, v___x_4547_);
lean_dec(v___x_4547_);
v___x_4549_ = lean_nat_add(v___x_4521_, v_numParams_4542_);
v___x_4550_ = lean_nat_add(v___x_4549_, v_numIndices_4543_);
lean_dec(v___x_4549_);
v___x_4551_ = lean_unsigned_to_nat(2u);
v___x_4552_ = lean_nat_mul(v___x_4551_, v_numParams_4542_);
lean_dec(v_numParams_4542_);
v___x_4553_ = lean_nat_add(v___x_4521_, v___x_4552_);
lean_dec(v___x_4552_);
v___x_4554_ = lean_nat_mul(v___x_4551_, v_numIndices_4543_);
lean_dec(v_numIndices_4543_);
v___x_4555_ = lean_nat_add(v___x_4553_, v___x_4554_);
lean_dec(v___x_4554_);
lean_dec(v___x_4553_);
v___x_4556_ = lean_nat_add(v___x_4555_, v___x_4521_);
lean_dec(v___x_4555_);
v___x_4557_ = lean_st_ref_take(v___y_4517_);
v_env_4558_ = lean_ctor_get(v___x_4557_, 0);
v_nextMacroScope_4559_ = lean_ctor_get(v___x_4557_, 1);
v_ngen_4560_ = lean_ctor_get(v___x_4557_, 2);
v_auxDeclNGen_4561_ = lean_ctor_get(v___x_4557_, 3);
v_traceState_4562_ = lean_ctor_get(v___x_4557_, 4);
v_messages_4563_ = lean_ctor_get(v___x_4557_, 6);
v_infoState_4564_ = lean_ctor_get(v___x_4557_, 7);
v_snapshotTasks_4565_ = lean_ctor_get(v___x_4557_, 8);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v___x_4557_, 5);
lean_dec(v_unused_4631_);
v___x_4567_ = v___x_4557_;
v_isShared_4568_ = v_isSharedCheck_4630_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_snapshotTasks_4565_);
lean_inc(v_infoState_4564_);
lean_inc(v_messages_4563_);
lean_inc(v_traceState_4562_);
lean_inc(v_auxDeclNGen_4561_);
lean_inc(v_ngen_4560_);
lean_inc(v_nextMacroScope_4559_);
lean_inc(v_env_4558_);
lean_dec(v___x_4557_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4630_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 2, v___x_4556_);
lean_ctor_set(v___x_4508_, 1, v___x_4550_);
lean_ctor_set(v___x_4508_, 0, v___x_4548_);
v___x_4570_ = v___x_4508_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4548_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v___x_4550_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v___x_4556_);
v___x_4570_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4574_; 
lean_inc(v_declName_4498_);
v___x_4571_ = l_Lean_markNoConfusion(v_env_4558_, v_declName_4498_, v___x_4570_);
v___x_4572_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 5, v___x_4572_);
lean_ctor_set(v___x_4567_, 0, v___x_4571_);
v___x_4574_ = v___x_4567_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4571_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_nextMacroScope_4559_);
lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_ngen_4560_);
lean_ctor_set(v_reuseFailAlloc_4628_, 3, v_auxDeclNGen_4561_);
lean_ctor_set(v_reuseFailAlloc_4628_, 4, v_traceState_4562_);
lean_ctor_set(v_reuseFailAlloc_4628_, 5, v___x_4572_);
lean_ctor_set(v_reuseFailAlloc_4628_, 6, v_messages_4563_);
lean_ctor_set(v_reuseFailAlloc_4628_, 7, v_infoState_4564_);
lean_ctor_set(v_reuseFailAlloc_4628_, 8, v_snapshotTasks_4565_);
v___x_4574_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v_mctx_4577_; lean_object* v_zetaDeltaFVarIds_4578_; lean_object* v_postponed_4579_; lean_object* v_diag_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4626_; 
v___x_4575_ = lean_st_ref_put(v___y_4517_, v___x_4574_);
v___x_4576_ = lean_st_ref_take(v___y_4515_);
v_mctx_4577_ = lean_ctor_get(v___x_4576_, 0);
v_zetaDeltaFVarIds_4578_ = lean_ctor_get(v___x_4576_, 2);
v_postponed_4579_ = lean_ctor_get(v___x_4576_, 3);
v_diag_4580_ = lean_ctor_get(v___x_4576_, 4);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4576_, 1);
lean_dec(v_unused_4627_);
v___x_4582_ = v___x_4576_;
v_isShared_4583_ = v_isSharedCheck_4626_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_diag_4580_);
lean_inc(v_postponed_4579_);
lean_inc(v_zetaDeltaFVarIds_4578_);
lean_inc(v_mctx_4577_);
lean_dec(v___x_4576_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4626_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4584_; lean_object* v___x_4586_; 
v___x_4584_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_4583_ == 0)
{
lean_ctor_set(v___x_4582_, 1, v___x_4584_);
v___x_4586_ = v___x_4582_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_mctx_4577_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_zetaDeltaFVarIds_4578_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_postponed_4579_);
lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_diag_4580_);
v___x_4586_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v_env_4589_; lean_object* v_nextMacroScope_4590_; lean_object* v_ngen_4591_; lean_object* v_auxDeclNGen_4592_; lean_object* v_traceState_4593_; lean_object* v_messages_4594_; lean_object* v_infoState_4595_; lean_object* v_snapshotTasks_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4623_; 
v___x_4587_ = lean_st_ref_put(v___y_4515_, v___x_4586_);
v___x_4588_ = lean_st_ref_take(v___y_4517_);
v_env_4589_ = lean_ctor_get(v___x_4588_, 0);
v_nextMacroScope_4590_ = lean_ctor_get(v___x_4588_, 1);
v_ngen_4591_ = lean_ctor_get(v___x_4588_, 2);
v_auxDeclNGen_4592_ = lean_ctor_get(v___x_4588_, 3);
v_traceState_4593_ = lean_ctor_get(v___x_4588_, 4);
v_messages_4594_ = lean_ctor_get(v___x_4588_, 6);
v_infoState_4595_ = lean_ctor_get(v___x_4588_, 7);
v_snapshotTasks_4596_ = lean_ctor_get(v___x_4588_, 8);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4588_);
if (v_isSharedCheck_4623_ == 0)
{
lean_object* v_unused_4624_; 
v_unused_4624_ = lean_ctor_get(v___x_4588_, 5);
lean_dec(v_unused_4624_);
v___x_4598_ = v___x_4588_;
v_isShared_4599_ = v_isSharedCheck_4623_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_snapshotTasks_4596_);
lean_inc(v_infoState_4595_);
lean_inc(v_messages_4594_);
lean_inc(v_traceState_4593_);
lean_inc(v_auxDeclNGen_4592_);
lean_inc(v_ngen_4591_);
lean_inc(v_nextMacroScope_4590_);
lean_inc(v_env_4589_);
lean_dec(v___x_4588_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4623_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4600_ = l_Lean_addProtected(v_env_4589_, v_declName_4498_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 5, v___x_4572_);
lean_ctor_set(v___x_4598_, 0, v___x_4600_);
v___x_4602_ = v___x_4598_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_nextMacroScope_4590_);
lean_ctor_set(v_reuseFailAlloc_4622_, 2, v_ngen_4591_);
lean_ctor_set(v_reuseFailAlloc_4622_, 3, v_auxDeclNGen_4592_);
lean_ctor_set(v_reuseFailAlloc_4622_, 4, v_traceState_4593_);
lean_ctor_set(v_reuseFailAlloc_4622_, 5, v___x_4572_);
lean_ctor_set(v_reuseFailAlloc_4622_, 6, v_messages_4594_);
lean_ctor_set(v_reuseFailAlloc_4622_, 7, v_infoState_4595_);
lean_ctor_set(v_reuseFailAlloc_4622_, 8, v_snapshotTasks_4596_);
v___x_4602_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v_mctx_4605_; lean_object* v_zetaDeltaFVarIds_4606_; lean_object* v_postponed_4607_; lean_object* v_diag_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4620_; 
v___x_4603_ = lean_st_ref_put(v___y_4517_, v___x_4602_);
v___x_4604_ = lean_st_ref_take(v___y_4515_);
v_mctx_4605_ = lean_ctor_get(v___x_4604_, 0);
v_zetaDeltaFVarIds_4606_ = lean_ctor_get(v___x_4604_, 2);
v_postponed_4607_ = lean_ctor_get(v___x_4604_, 3);
v_diag_4608_ = lean_ctor_get(v___x_4604_, 4);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4620_ == 0)
{
lean_object* v_unused_4621_; 
v_unused_4621_ = lean_ctor_get(v___x_4604_, 1);
lean_dec(v_unused_4621_);
v___x_4610_ = v___x_4604_;
v_isShared_4611_ = v_isSharedCheck_4620_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_diag_4608_);
lean_inc(v_postponed_4607_);
lean_inc(v_zetaDeltaFVarIds_4606_);
lean_inc(v_mctx_4605_);
lean_dec(v___x_4604_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4620_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4612_; lean_object* v___x_4614_; 
v___x_4612_ = lean_box(0);
if (v_isShared_4611_ == 0)
{
lean_ctor_set(v___x_4610_, 1, v___x_4584_);
v___x_4614_ = v___x_4610_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_mctx_4605_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___x_4584_);
lean_ctor_set(v_reuseFailAlloc_4619_, 2, v_zetaDeltaFVarIds_4606_);
lean_ctor_set(v_reuseFailAlloc_4619_, 3, v_postponed_4607_);
lean_ctor_set(v_reuseFailAlloc_4619_, 4, v_diag_4608_);
v___x_4614_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4615_; lean_object* v___x_4617_; 
v___x_4615_ = lean_st_ref_put(v___y_4515_, v___x_4614_);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4612_);
v___x_4617_ = v___x_4540_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4612_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
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
lean_del_object(v___x_4508_);
lean_dec_ref(v_val_4502_);
lean_dec(v_declName_4498_);
return v___x_4537_;
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec(v_a_4526_);
lean_del_object(v___x_4508_);
lean_dec(v_levelParams_4506_);
lean_dec_ref(v_val_4502_);
lean_dec(v_declName_4498_);
v_a_4636_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4527_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4527_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_del_object(v___x_4508_);
lean_dec(v_levelParams_4506_);
lean_dec_ref(v_val_4502_);
lean_dec(v_declName_4498_);
v_a_4644_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4525_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4525_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec_ref(v___x_4518_);
lean_dec_ref_known(v___x_4511_, 2);
lean_dec(v_tail_4512_);
lean_del_object(v___x_4508_);
lean_dec(v_levelParams_4506_);
lean_dec(v___x_4503_);
lean_dec_ref(v_val_4502_);
lean_dec(v_declName_4498_);
v_a_4652_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4519_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4519_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
}
else
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_dec(v___x_4511_);
lean_del_object(v___x_4508_);
lean_dec(v_levelParams_4506_);
lean_dec(v___x_4503_);
lean_dec_ref(v_val_4502_);
lean_dec(v_noConfusionTypeName_4499_);
lean_dec(v_declName_4498_);
v___x_4671_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__6);
v___x_4672_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_4671_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4672_;
}
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4683_; 
lean_dec(v___x_4503_);
lean_dec_ref(v_val_4502_);
lean_dec(v_noConfusionTypeName_4499_);
lean_dec(v_declName_4498_);
v_a_4676_ = lean_ctor_get(v___x_4504_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4678_ = v___x_4504_;
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4504_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4683_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4681_; 
if (v_isShared_4679_ == 0)
{
v___x_4681_ = v___x_4678_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
v___x_4681_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
return v___x_4681_;
}
}
}
}
else
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
lean_dec(v_a_4501_);
lean_dec(v_noConfusionTypeName_4499_);
lean_dec(v_declName_4498_);
lean_dec(v_indName_4490_);
v___x_4684_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__7);
v___x_4685_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_4684_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4685_;
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_noConfusionTypeName_4499_);
lean_dec(v_declName_4498_);
lean_dec(v_indName_4490_);
v_a_4686_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4500_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4500_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___boxed(lean_object* v_indName_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(v_indName_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_);
lean_dec(v_a_4698_);
lean_dec_ref(v_a_4697_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3(lean_object* v_00_u03b1_4701_, lean_object* v_bs_4702_, lean_object* v_k_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v___x_4709_; 
v___x_4709_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___redArg(v_bs_4702_, v_k_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
return v___x_4709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3___boxed(lean_object* v_00_u03b1_4710_, lean_object* v_bs_4711_, lean_object* v_k_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2_spec__3(v_00_u03b1_4710_, v_bs_4711_, v_k_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec(v___y_4714_);
lean_dec_ref(v___y_4713_);
lean_dec_ref(v_bs_4711_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2(lean_object* v_00_u03b1_4719_, lean_object* v_bs_4720_, lean_object* v_k_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v___x_4727_; 
v___x_4727_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___redArg(v_bs_4720_, v_k_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed(lean_object* v_00_u03b1_4728_, lean_object* v_bs_4729_, lean_object* v_k_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2(v_00_u03b1_4728_, v_bs_4729_, v_k_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4733_);
lean_dec(v___y_4732_);
lean_dec_ref(v___y_4731_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(lean_object* v_declName_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
lean_inc(v_declName_4737_);
v___x_4743_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4779_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4746_ = v___x_4743_;
v_isShared_4747_ = v_isSharedCheck_4779_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4743_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4779_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
if (lean_obj_tag(v_a_4744_) == 5)
{
lean_object* v_val_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; 
lean_del_object(v___x_4746_);
v_val_4748_ = lean_ctor_get(v_a_4744_, 0);
lean_inc_ref(v_val_4748_);
lean_dec_ref_known(v_a_4744_, 1);
v___x_4749_ = l_Lean_mkRecName(v_declName_4737_);
v___x_4750_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_4749_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v_toConstantVal_4751_; lean_object* v_a_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4765_; 
v_toConstantVal_4751_ = lean_ctor_get(v_val_4748_, 0);
lean_inc_ref(v_toConstantVal_4751_);
lean_dec_ref(v_val_4748_);
v_a_4752_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4754_ = v___x_4750_;
v_isShared_4755_ = v_isSharedCheck_4765_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_a_4752_);
lean_dec(v___x_4750_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4765_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v_levelParams_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; uint8_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4763_; 
v_levelParams_4756_ = lean_ctor_get(v_toConstantVal_4751_, 1);
lean_inc(v_levelParams_4756_);
lean_dec_ref(v_toConstantVal_4751_);
v___x_4757_ = l_List_lengthTR___redArg(v_levelParams_4756_);
lean_dec(v_levelParams_4756_);
v___x_4758_ = l_Lean_ConstantInfo_levelParams(v_a_4752_);
lean_dec(v_a_4752_);
v___x_4759_ = l_List_lengthTR___redArg(v___x_4758_);
lean_dec(v___x_4758_);
v___x_4760_ = lean_nat_dec_lt(v___x_4757_, v___x_4759_);
lean_dec(v___x_4759_);
lean_dec(v___x_4757_);
v___x_4761_ = lean_box(v___x_4760_);
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 0, v___x_4761_);
v___x_4763_ = v___x_4754_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v___x_4761_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_dec_ref(v_val_4748_);
v_a_4766_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4750_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4750_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
else
{
uint8_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4777_; 
lean_dec(v_a_4744_);
lean_dec(v_declName_4737_);
v___x_4774_ = 0;
v___x_4775_ = lean_box(v___x_4774_);
if (v_isShared_4747_ == 0)
{
lean_ctor_set(v___x_4746_, 0, v___x_4775_);
v___x_4777_ = v___x_4746_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4775_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4787_; 
lean_dec(v_declName_4737_);
v_a_4780_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4787_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4787_ == 0)
{
v___x_4782_ = v___x_4743_;
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4743_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4787_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4785_; 
if (v_isShared_4783_ == 0)
{
v___x_4785_ = v___x_4782_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4786_; 
v_reuseFailAlloc_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4780_);
v___x_4785_ = v_reuseFailAlloc_4786_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
return v___x_4785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___boxed(lean_object* v_declName_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(v_declName_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(lean_object* v_as_4795_, size_t v_sz_4796_, size_t v_i_4797_, lean_object* v_b_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_a_4805_; uint8_t v___x_4809_; 
v___x_4809_ = lean_usize_dec_lt(v_i_4797_, v_sz_4796_);
if (v___x_4809_ == 0)
{
lean_object* v___x_4810_; 
v___x_4810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4810_, 0, v_b_4798_);
return v___x_4810_;
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4812_; 
v_a_4811_ = lean_array_uget_borrowed(v_as_4795_, v_i_4797_);
lean_inc(v___y_4802_);
lean_inc_ref(v___y_4801_);
lean_inc(v___y_4800_);
lean_inc_ref(v___y_4799_);
lean_inc_ref(v_b_4798_);
v___x_4812_ = lean_infer_type(v_b_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4814_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
lean_inc(v_a_4813_);
lean_dec_ref_known(v___x_4812_, 1);
v___x_4814_ = l_Lean_Meta_whnfForall(v_a_4813_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v___x_4816_ = l_Lean_Expr_bindingDomain_x21(v_a_4815_);
lean_dec(v_a_4815_);
v___x_4817_ = l_Lean_Expr_isHEq(v___x_4816_);
lean_dec_ref(v___x_4816_);
lean_inc(v___y_4802_);
lean_inc_ref(v___y_4801_);
lean_inc(v___y_4800_);
lean_inc_ref(v___y_4799_);
lean_inc(v_a_4811_);
v___x_4818_ = lean_infer_type(v_a_4811_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4818_) == 0)
{
lean_object* v_a_4819_; 
v_a_4819_ = lean_ctor_get(v___x_4818_, 0);
lean_inc(v_a_4819_);
lean_dec_ref_known(v___x_4818_, 1);
if (v___x_4817_ == 0)
{
lean_dec(v_a_4819_);
goto v___jp_4820_;
}
else
{
uint8_t v___x_4822_; 
v___x_4822_ = l_Lean_Expr_isEq(v_a_4819_);
lean_dec(v_a_4819_);
if (v___x_4822_ == 0)
{
goto v___jp_4820_;
}
else
{
lean_object* v___x_4823_; 
lean_inc(v_a_4811_);
v___x_4823_ = l_Lean_Meta_mkHEqOfEq(v_a_4811_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4825_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref_known(v___x_4823_, 1);
v___x_4825_ = l_Lean_Expr_app___override(v_b_4798_, v_a_4824_);
v_a_4805_ = v___x_4825_;
goto v___jp_4804_;
}
else
{
lean_dec_ref(v_b_4798_);
return v___x_4823_;
}
}
}
v___jp_4820_:
{
lean_object* v___x_4821_; 
lean_inc(v_a_4811_);
v___x_4821_ = l_Lean_Expr_app___override(v_b_4798_, v_a_4811_);
v_a_4805_ = v___x_4821_;
goto v___jp_4804_;
}
}
else
{
lean_dec_ref(v_b_4798_);
return v___x_4818_;
}
}
else
{
lean_dec_ref(v_b_4798_);
return v___x_4814_;
}
}
else
{
lean_dec_ref(v_b_4798_);
return v___x_4812_;
}
}
v___jp_4804_:
{
size_t v___x_4806_; size_t v___x_4807_; 
v___x_4806_ = ((size_t)1ULL);
v___x_4807_ = lean_usize_add(v_i_4797_, v___x_4806_);
v_i_4797_ = v___x_4807_;
v_b_4798_ = v_a_4805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___boxed(lean_object* v_as_4826_, lean_object* v_sz_4827_, lean_object* v_i_4828_, lean_object* v_b_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
size_t v_sz_boxed_4835_; size_t v_i_boxed_4836_; lean_object* v_res_4837_; 
v_sz_boxed_4835_ = lean_unbox_usize(v_sz_4827_);
lean_dec(v_sz_4827_);
v_i_boxed_4836_ = lean_unbox_usize(v_i_4828_);
lean_dec(v_i_4828_);
v_res_4837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(v_as_4826_, v_sz_boxed_4835_, v_i_boxed_4836_, v_b_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec_ref(v_as_4826_);
return v_res_4837_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__0));
v___x_4840_ = l_Lean_stringToMessageData(v___x_4839_);
return v___x_4840_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__2));
v___x_4843_ = l_Lean_stringToMessageData(v___x_4842_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg(lean_object* v_range_4844_, lean_object* v_b_4845_, lean_object* v_i_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v_stop_4852_; lean_object* v_step_4853_; lean_object* v_a_4855_; uint8_t v___x_4858_; 
v_stop_4852_ = lean_ctor_get(v_range_4844_, 1);
v_step_4853_ = lean_ctor_get(v_range_4844_, 2);
v___x_4858_ = lean_nat_dec_lt(v_i_4846_, v_stop_4852_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; 
lean_dec(v_i_4846_);
v___x_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4859_, 0, v_b_4845_);
return v___x_4859_;
}
else
{
lean_object* v___x_4860_; 
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
lean_inc_ref(v___y_4847_);
lean_inc_ref(v_b_4845_);
v___x_4860_ = lean_infer_type(v_b_4845_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = l_Lean_Meta_whnfForall(v_a_4861_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v___x_4864_ = l_Lean_Expr_bindingDomain_x21(v_a_4863_);
lean_dec(v_a_4863_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
lean_inc_ref(v___y_4847_);
v___x_4865_ = lean_whnf(v___x_4864_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; uint8_t v___x_4869_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4865_, 1);
v___x_4867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1));
v___x_4868_ = lean_unsigned_to_nat(4u);
v___x_4869_ = l_Lean_Expr_isAppOfArity(v_a_4866_, v___x_4867_, v___x_4868_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v___x_4872_; 
v___x_4870_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__0));
v___x_4871_ = lean_unsigned_to_nat(3u);
v___x_4872_ = l_Lean_Expr_isAppOfArity(v_a_4866_, v___x_4870_, v___x_4871_);
if (v___x_4872_ == 0)
{
lean_object* v___x_4873_; 
lean_dec(v_i_4846_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
lean_inc_ref(v___y_4847_);
v___x_4873_ = lean_infer_type(v_b_4845_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v___x_4873_, 1);
v___x_4875_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__1);
v___x_4876_ = l_Lean_MessageData_ofExpr(v_a_4866_);
v___x_4877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___closed__3);
v___x_4879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = lean_unsigned_to_nat(30u);
v___x_4881_ = l_Lean_inlineExpr(v_a_4874_, v___x_4880_);
v___x_4882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4882_, 0, v___x_4879_);
lean_ctor_set(v___x_4882_, 1, v___x_4881_);
v___x_4883_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_4882_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4883_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4883_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_dec(v_a_4866_);
return v___x_4873_;
}
}
else
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = l_Lean_Expr_appFn_x21(v_a_4866_);
lean_dec(v_a_4866_);
v___x_4893_ = l_Lean_Expr_appArg_x21(v___x_4892_);
lean_dec_ref(v___x_4892_);
v___x_4894_ = l_Lean_Meta_mkEqRefl(v___x_4893_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4894_) == 0)
{
lean_object* v_a_4895_; lean_object* v___x_4896_; 
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc(v_a_4895_);
lean_dec_ref_known(v___x_4894_, 1);
v___x_4896_ = l_Lean_Expr_app___override(v_b_4845_, v_a_4895_);
v_a_4855_ = v___x_4896_;
goto v___jp_4854_;
}
else
{
lean_dec(v_i_4846_);
lean_dec_ref(v_b_4845_);
return v___x_4894_;
}
}
}
else
{
lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4897_ = l_Lean_Expr_appFn_x21(v_a_4866_);
lean_dec(v_a_4866_);
v___x_4898_ = l_Lean_Expr_appFn_x21(v___x_4897_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = l_Lean_Expr_appArg_x21(v___x_4898_);
lean_dec_ref(v___x_4898_);
v___x_4900_ = l_Lean_Meta_mkHEqRefl(v___x_4899_, v___y_4847_, v___y_4848_, v___y_4849_, v___y_4850_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4901_; lean_object* v___x_4902_; 
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
lean_inc(v_a_4901_);
lean_dec_ref_known(v___x_4900_, 1);
v___x_4902_ = l_Lean_Expr_app___override(v_b_4845_, v_a_4901_);
v_a_4855_ = v___x_4902_;
goto v___jp_4854_;
}
else
{
lean_dec(v_i_4846_);
lean_dec_ref(v_b_4845_);
return v___x_4900_;
}
}
}
else
{
lean_dec(v_i_4846_);
lean_dec_ref(v_b_4845_);
return v___x_4865_;
}
}
else
{
lean_dec(v_i_4846_);
lean_dec_ref(v_b_4845_);
return v___x_4862_;
}
}
else
{
lean_dec(v_i_4846_);
lean_dec_ref(v_b_4845_);
return v___x_4860_;
}
}
v___jp_4854_:
{
lean_object* v___x_4856_; 
v___x_4856_ = lean_nat_add(v_i_4846_, v_step_4853_);
lean_dec(v_i_4846_);
v_b_4845_ = v_a_4855_;
v_i_4846_ = v___x_4856_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg___boxed(lean_object* v_range_4903_, lean_object* v_b_4904_, lean_object* v_i_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg(v_range_4903_, v_b_4904_, v_i_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec_ref(v_range_4903_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0(lean_object* v___x_4912_, lean_object* v___x_4913_, lean_object* v___x_4914_, lean_object* v_xs_4915_, lean_object* v___x_4916_, lean_object* v___x_4917_, lean_object* v___x_4918_, lean_object* v___x_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v_eqs_4923_, lean_object* v_P_4924_, lean_object* v___x_4925_, lean_object* v_eqvs_4926_, uint8_t v_a_4927_, uint8_t v_a_4928_, lean_object* v_head_4929_, lean_object* v___x_4930_, lean_object* v_a_4931_, lean_object* v_numParams_4932_, lean_object* v_numFields_4933_, lean_object* v___x_4934_, lean_object* v___x_4935_, lean_object* v_k_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4942_ = l_Lean_mkConst(v___x_4912_, v___x_4913_);
v___x_4943_ = l_Array_append___redArg(v___x_4914_, v_xs_4915_);
v___x_4944_ = l_Array_append___redArg(v___x_4943_, v___x_4916_);
lean_inc_ref_n(v___x_4917_, 2);
v___x_4945_ = lean_array_push(v___x_4917_, v___x_4918_);
v___x_4946_ = l_Array_append___redArg(v___x_4944_, v___x_4945_);
lean_dec_ref(v___x_4945_);
v___x_4947_ = l_Array_append___redArg(v___x_4946_, v_xs_4915_);
v___x_4948_ = l_Array_append___redArg(v___x_4947_, v___x_4919_);
v___x_4949_ = lean_array_push(v___x_4917_, v___x_4920_);
v___x_4950_ = l_Array_append___redArg(v___x_4948_, v___x_4949_);
lean_dec_ref(v___x_4949_);
v___x_4951_ = l_Lean_mkAppN(v___x_4942_, v___x_4950_);
lean_dec_ref(v___x_4950_);
v___x_4952_ = lean_array_get_size(v_xs_4915_);
lean_inc(v___x_4922_);
lean_inc(v___x_4921_);
v___x_4953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4921_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
lean_ctor_set(v___x_4953_, 2, v___x_4922_);
v___x_4954_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg(v___x_4953_, v___x_4951_, v___x_4921_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
lean_dec_ref_known(v___x_4953_, 3);
if (lean_obj_tag(v___x_4954_) == 0)
{
lean_object* v_a_4955_; size_t v_sz_4956_; size_t v___x_4957_; lean_object* v___x_4958_; 
v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
lean_inc(v_a_4955_);
lean_dec_ref_known(v___x_4954_, 1);
v_sz_4956_ = lean_array_size(v_eqs_4923_);
v___x_4957_ = ((size_t)0ULL);
v___x_4958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(v_eqs_4923_, v_sz_4956_, v___x_4957_, v_a_4955_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref_known(v___x_4958_, 1);
lean_inc_ref(v_k_4936_);
v___x_4960_ = l_Lean_Expr_app___override(v_a_4959_, v_k_4936_);
v___x_4961_ = l_Lean_Meta_mkExpectedTypeHint(v___x_4960_, v_P_4924_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4961_) == 0)
{
lean_object* v_a_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; lean_object* v___x_4967_; 
v_a_4962_ = lean_ctor_get(v___x_4961_, 0);
lean_inc(v_a_4962_);
lean_dec_ref_known(v___x_4961_, 1);
v___x_4963_ = l_Array_append___redArg(v___x_4925_, v_eqvs_4926_);
v___x_4964_ = lean_array_push(v___x_4917_, v_k_4936_);
v___x_4965_ = l_Array_append___redArg(v___x_4963_, v___x_4964_);
lean_dec_ref(v___x_4964_);
v___x_4966_ = 1;
v___x_4967_ = l_Lean_Meta_mkLambdaFVars(v___x_4965_, v_a_4962_, v_a_4927_, v_a_4928_, v_a_4927_, v_a_4928_, v___x_4966_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
lean_dec_ref(v___x_4965_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_n(v_a_4968_, 2);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4969_ = l_Lean_Name_str___override(v_head_4929_, v___x_4930_);
lean_inc(v___y_4940_);
lean_inc_ref(v___y_4939_);
lean_inc(v___y_4938_);
lean_inc_ref(v___y_4937_);
v___x_4970_ = lean_infer_type(v_a_4968_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5035_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
v___x_4972_ = l_Lean_ConstantInfo_levelParams(v_a_4931_);
v___x_4973_ = lean_box(1);
lean_inc(v___x_4969_);
v___x_4974_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v___x_4969_, v___x_4972_, v_a_4971_, v_a_4968_, v___x_4973_, v___y_4940_);
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_5035_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_5035_ == 0)
{
v___x_4977_ = v___x_4974_;
v_isShared_4978_ = v_isSharedCheck_5035_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4974_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5035_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
lean_ctor_set_tag(v___x_4977_, 1);
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_5034_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
lean_object* v___x_4981_; 
v___x_4981_ = l_Lean_addDecl(v___x_4980_, v_a_4927_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4981_) == 0)
{
lean_object* v___x_4982_; lean_object* v___x_4984_; uint8_t v_isShared_4985_; uint8_t v_isSharedCheck_5032_; 
lean_dec_ref_known(v___x_4981_, 1);
lean_inc(v___x_4969_);
v___x_4982_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_4969_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5032_ == 0)
{
lean_object* v_unused_5033_; 
v_unused_5033_ = lean_ctor_get(v___x_4982_, 0);
lean_dec(v_unused_5033_);
v___x_4984_ = v___x_4982_;
v_isShared_4985_ = v_isSharedCheck_5032_;
goto v_resetjp_4983_;
}
else
{
lean_dec(v___x_4982_);
v___x_4984_ = lean_box(0);
v_isShared_4985_ = v_isSharedCheck_5032_;
goto v_resetjp_4983_;
}
v_resetjp_4983_:
{
lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v_env_4994_; lean_object* v_nextMacroScope_4995_; lean_object* v_ngen_4996_; lean_object* v_auxDeclNGen_4997_; lean_object* v_traceState_4998_; lean_object* v_messages_4999_; lean_object* v_infoState_5000_; lean_object* v_snapshotTasks_5001_; lean_object* v___x_5003_; uint8_t v_isShared_5004_; uint8_t v_isSharedCheck_5030_; 
v___x_4986_ = lean_nat_add(v_numParams_4932_, v___x_4922_);
lean_dec(v___x_4922_);
v___x_4987_ = lean_unsigned_to_nat(2u);
v___x_4988_ = lean_nat_mul(v___x_4987_, v_numFields_4933_);
v___x_4989_ = lean_nat_add(v___x_4986_, v___x_4988_);
lean_dec(v___x_4988_);
lean_dec(v___x_4986_);
v___x_4990_ = lean_array_get_size(v_eqvs_4926_);
v___x_4991_ = lean_nat_add(v___x_4989_, v___x_4990_);
lean_dec(v___x_4989_);
v___x_4992_ = l_Lean_Expr_getNumHeadForalls(v___x_4934_);
v___x_4993_ = lean_st_ref_take(v___y_4940_);
v_env_4994_ = lean_ctor_get(v___x_4993_, 0);
v_nextMacroScope_4995_ = lean_ctor_get(v___x_4993_, 1);
v_ngen_4996_ = lean_ctor_get(v___x_4993_, 2);
v_auxDeclNGen_4997_ = lean_ctor_get(v___x_4993_, 3);
v_traceState_4998_ = lean_ctor_get(v___x_4993_, 4);
v_messages_4999_ = lean_ctor_get(v___x_4993_, 6);
v_infoState_5000_ = lean_ctor_get(v___x_4993_, 7);
v_snapshotTasks_5001_ = lean_ctor_get(v___x_4993_, 8);
v_isSharedCheck_5030_ = !lean_is_exclusive(v___x_4993_);
if (v_isSharedCheck_5030_ == 0)
{
lean_object* v_unused_5031_; 
v_unused_5031_ = lean_ctor_get(v___x_4993_, 5);
lean_dec(v_unused_5031_);
v___x_5003_ = v___x_4993_;
v_isShared_5004_ = v_isSharedCheck_5030_;
goto v_resetjp_5002_;
}
else
{
lean_inc(v_snapshotTasks_5001_);
lean_inc(v_infoState_5000_);
lean_inc(v_messages_4999_);
lean_inc(v_traceState_4998_);
lean_inc(v_auxDeclNGen_4997_);
lean_inc(v_ngen_4996_);
lean_inc(v_nextMacroScope_4995_);
lean_inc(v_env_4994_);
lean_dec(v___x_4993_);
v___x_5003_ = lean_box(0);
v_isShared_5004_ = v_isSharedCheck_5030_;
goto v_resetjp_5002_;
}
v_resetjp_5002_:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5009_; 
v___x_5005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_4991_);
lean_ctor_set(v___x_5005_, 1, v___x_4992_);
v___x_5006_ = l_Lean_markNoConfusion(v_env_4994_, v___x_4969_, v___x_5005_);
v___x_5007_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_5004_ == 0)
{
lean_ctor_set(v___x_5003_, 5, v___x_5007_);
lean_ctor_set(v___x_5003_, 0, v___x_5006_);
v___x_5009_ = v___x_5003_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v___x_5006_);
lean_ctor_set(v_reuseFailAlloc_5029_, 1, v_nextMacroScope_4995_);
lean_ctor_set(v_reuseFailAlloc_5029_, 2, v_ngen_4996_);
lean_ctor_set(v_reuseFailAlloc_5029_, 3, v_auxDeclNGen_4997_);
lean_ctor_set(v_reuseFailAlloc_5029_, 4, v_traceState_4998_);
lean_ctor_set(v_reuseFailAlloc_5029_, 5, v___x_5007_);
lean_ctor_set(v_reuseFailAlloc_5029_, 6, v_messages_4999_);
lean_ctor_set(v_reuseFailAlloc_5029_, 7, v_infoState_5000_);
lean_ctor_set(v_reuseFailAlloc_5029_, 8, v_snapshotTasks_5001_);
v___x_5009_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v_mctx_5012_; lean_object* v_zetaDeltaFVarIds_5013_; lean_object* v_postponed_5014_; lean_object* v_diag_5015_; lean_object* v___x_5017_; uint8_t v_isShared_5018_; uint8_t v_isSharedCheck_5027_; 
v___x_5010_ = lean_st_ref_put(v___y_4940_, v___x_5009_);
v___x_5011_ = lean_st_ref_take(v___y_4938_);
v_mctx_5012_ = lean_ctor_get(v___x_5011_, 0);
v_zetaDeltaFVarIds_5013_ = lean_ctor_get(v___x_5011_, 2);
v_postponed_5014_ = lean_ctor_get(v___x_5011_, 3);
v_diag_5015_ = lean_ctor_get(v___x_5011_, 4);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5027_ == 0)
{
lean_object* v_unused_5028_; 
v_unused_5028_ = lean_ctor_get(v___x_5011_, 1);
lean_dec(v_unused_5028_);
v___x_5017_ = v___x_5011_;
v_isShared_5018_ = v_isSharedCheck_5027_;
goto v_resetjp_5016_;
}
else
{
lean_inc(v_diag_5015_);
lean_inc(v_postponed_5014_);
lean_inc(v_zetaDeltaFVarIds_5013_);
lean_inc(v_mctx_5012_);
lean_dec(v___x_5011_);
v___x_5017_ = lean_box(0);
v_isShared_5018_ = v_isSharedCheck_5027_;
goto v_resetjp_5016_;
}
v_resetjp_5016_:
{
lean_object* v___x_5019_; lean_object* v___x_5021_; 
v___x_5019_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_5018_ == 0)
{
lean_ctor_set(v___x_5017_, 1, v___x_5019_);
v___x_5021_ = v___x_5017_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_mctx_5012_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v___x_5019_);
lean_ctor_set(v_reuseFailAlloc_5026_, 2, v_zetaDeltaFVarIds_5013_);
lean_ctor_set(v_reuseFailAlloc_5026_, 3, v_postponed_5014_);
lean_ctor_set(v_reuseFailAlloc_5026_, 4, v_diag_5015_);
v___x_5021_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5022_ = lean_st_ref_put(v___y_4938_, v___x_5021_);
if (v_isShared_4985_ == 0)
{
lean_ctor_set(v___x_4984_, 0, v___x_4935_);
v___x_5024_ = v___x_4984_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_4935_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_4969_);
lean_dec(v___x_4922_);
return v___x_4981_;
}
}
}
}
else
{
lean_object* v_a_5036_; lean_object* v___x_5038_; uint8_t v_isShared_5039_; uint8_t v_isSharedCheck_5043_; 
lean_dec(v___x_4969_);
lean_dec(v_a_4968_);
lean_dec(v___x_4922_);
v_a_5036_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_5043_ == 0)
{
v___x_5038_ = v___x_4970_;
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
else
{
lean_inc(v_a_5036_);
lean_dec(v___x_4970_);
v___x_5038_ = lean_box(0);
v_isShared_5039_ = v_isSharedCheck_5043_;
goto v_resetjp_5037_;
}
v_resetjp_5037_:
{
lean_object* v___x_5041_; 
if (v_isShared_5039_ == 0)
{
v___x_5041_ = v___x_5038_;
goto v_reusejp_5040_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
v___x_5041_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5040_;
}
v_reusejp_5040_:
{
return v___x_5041_;
}
}
}
}
else
{
lean_object* v_a_5044_; lean_object* v___x_5046_; uint8_t v_isShared_5047_; uint8_t v_isSharedCheck_5051_; 
lean_dec_ref(v___x_4930_);
lean_dec(v_head_4929_);
lean_dec(v___x_4922_);
v_a_5044_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_5051_ == 0)
{
v___x_5046_ = v___x_4967_;
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
else
{
lean_inc(v_a_5044_);
lean_dec(v___x_4967_);
v___x_5046_ = lean_box(0);
v_isShared_5047_ = v_isSharedCheck_5051_;
goto v_resetjp_5045_;
}
v_resetjp_5045_:
{
lean_object* v___x_5049_; 
if (v_isShared_5047_ == 0)
{
v___x_5049_ = v___x_5046_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
v___x_5049_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
return v___x_5049_;
}
}
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
lean_dec_ref(v_k_4936_);
lean_dec_ref(v___x_4930_);
lean_dec(v_head_4929_);
lean_dec_ref(v___x_4925_);
lean_dec(v___x_4922_);
lean_dec_ref(v___x_4917_);
v_a_5052_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_4961_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_4961_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
lean_dec_ref(v_k_4936_);
lean_dec_ref(v___x_4930_);
lean_dec(v_head_4929_);
lean_dec_ref(v___x_4925_);
lean_dec_ref(v_P_4924_);
lean_dec(v___x_4922_);
lean_dec_ref(v___x_4917_);
v_a_5060_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_4958_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_4958_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
return v___x_5065_;
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec_ref(v_k_4936_);
lean_dec_ref(v___x_4930_);
lean_dec(v_head_4929_);
lean_dec_ref(v___x_4925_);
lean_dec_ref(v_P_4924_);
lean_dec(v___x_4922_);
lean_dec_ref(v___x_4917_);
v_a_5068_ = lean_ctor_get(v___x_4954_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_4954_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_4954_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_4954_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5076_ = _args[0];
lean_object* v___x_5077_ = _args[1];
lean_object* v___x_5078_ = _args[2];
lean_object* v_xs_5079_ = _args[3];
lean_object* v___x_5080_ = _args[4];
lean_object* v___x_5081_ = _args[5];
lean_object* v___x_5082_ = _args[6];
lean_object* v___x_5083_ = _args[7];
lean_object* v___x_5084_ = _args[8];
lean_object* v___x_5085_ = _args[9];
lean_object* v___x_5086_ = _args[10];
lean_object* v_eqs_5087_ = _args[11];
lean_object* v_P_5088_ = _args[12];
lean_object* v___x_5089_ = _args[13];
lean_object* v_eqvs_5090_ = _args[14];
lean_object* v_a_5091_ = _args[15];
lean_object* v_a_5092_ = _args[16];
lean_object* v_head_5093_ = _args[17];
lean_object* v___x_5094_ = _args[18];
lean_object* v_a_5095_ = _args[19];
lean_object* v_numParams_5096_ = _args[20];
lean_object* v_numFields_5097_ = _args[21];
lean_object* v___x_5098_ = _args[22];
lean_object* v___x_5099_ = _args[23];
lean_object* v_k_5100_ = _args[24];
lean_object* v___y_5101_ = _args[25];
lean_object* v___y_5102_ = _args[26];
lean_object* v___y_5103_ = _args[27];
lean_object* v___y_5104_ = _args[28];
lean_object* v___y_5105_ = _args[29];
_start:
{
uint8_t v_a_17861__boxed_5106_; uint8_t v_a_17862__boxed_5107_; lean_object* v_res_5108_; 
v_a_17861__boxed_5106_ = lean_unbox(v_a_5091_);
v_a_17862__boxed_5107_ = lean_unbox(v_a_5092_);
v_res_5108_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0(v___x_5076_, v___x_5077_, v___x_5078_, v_xs_5079_, v___x_5080_, v___x_5081_, v___x_5082_, v___x_5083_, v___x_5084_, v___x_5085_, v___x_5086_, v_eqs_5087_, v_P_5088_, v___x_5089_, v_eqvs_5090_, v_a_17861__boxed_5106_, v_a_17862__boxed_5107_, v_head_5093_, v___x_5094_, v_a_5095_, v_numParams_5096_, v_numFields_5097_, v___x_5098_, v___x_5099_, v_k_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
lean_dec_ref(v___x_5098_);
lean_dec(v_numFields_5097_);
lean_dec(v_numParams_5096_);
lean_dec_ref(v_a_5095_);
lean_dec_ref(v_eqvs_5090_);
lean_dec_ref(v_eqs_5087_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec_ref(v_xs_5079_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1(lean_object* v_head_5109_, lean_object* v_P_5110_, lean_object* v___x_5111_, lean_object* v_xs_5112_, lean_object* v_fields2_5113_, lean_object* v___x_5114_, lean_object* v___x_5115_, lean_object* v___x_5116_, lean_object* v___x_5117_, lean_object* v___x_5118_, lean_object* v___x_5119_, lean_object* v___x_5120_, lean_object* v___x_5121_, lean_object* v___x_5122_, lean_object* v___x_5123_, lean_object* v___x_5124_, uint8_t v_a_5125_, uint8_t v_a_5126_, lean_object* v___x_5127_, lean_object* v_a_5128_, lean_object* v_numParams_5129_, lean_object* v_numFields_5130_, lean_object* v___x_5131_, lean_object* v_eqvs_5132_, lean_object* v_eqs_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_){
_start:
{
lean_object* v___x_5139_; 
lean_inc_ref(v_P_5110_);
lean_inc(v_head_5109_);
v___x_5139_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_head_5109_, v_P_5110_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___f_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5139_, 1);
v___x_5141_ = l_Array_append___redArg(v___x_5111_, v_xs_5112_);
v___x_5142_ = l_Array_append___redArg(v___x_5141_, v_fields2_5113_);
v___x_5143_ = l_Lean_Expr_beta(v_a_5140_, v___x_5142_);
v___x_5144_ = lean_box(v_a_5125_);
v___x_5145_ = lean_box(v_a_5126_);
lean_inc_ref(v___x_5143_);
v___f_5146_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__0___boxed), 30, 24);
lean_closure_set(v___f_5146_, 0, v___x_5114_);
lean_closure_set(v___f_5146_, 1, v___x_5115_);
lean_closure_set(v___f_5146_, 2, v___x_5116_);
lean_closure_set(v___f_5146_, 3, v_xs_5112_);
lean_closure_set(v___f_5146_, 4, v___x_5117_);
lean_closure_set(v___f_5146_, 5, v___x_5118_);
lean_closure_set(v___f_5146_, 6, v___x_5119_);
lean_closure_set(v___f_5146_, 7, v___x_5120_);
lean_closure_set(v___f_5146_, 8, v___x_5121_);
lean_closure_set(v___f_5146_, 9, v___x_5122_);
lean_closure_set(v___f_5146_, 10, v___x_5123_);
lean_closure_set(v___f_5146_, 11, v_eqs_5133_);
lean_closure_set(v___f_5146_, 12, v_P_5110_);
lean_closure_set(v___f_5146_, 13, v___x_5124_);
lean_closure_set(v___f_5146_, 14, v_eqvs_5132_);
lean_closure_set(v___f_5146_, 15, v___x_5144_);
lean_closure_set(v___f_5146_, 16, v___x_5145_);
lean_closure_set(v___f_5146_, 17, v_head_5109_);
lean_closure_set(v___f_5146_, 18, v___x_5127_);
lean_closure_set(v___f_5146_, 19, v_a_5128_);
lean_closure_set(v___f_5146_, 20, v_numParams_5129_);
lean_closure_set(v___f_5146_, 21, v_numFields_5130_);
lean_closure_set(v___f_5146_, 22, v___x_5143_);
lean_closure_set(v___f_5146_, 23, v___x_5131_);
v___x_5147_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1));
v___x_5148_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5147_, v___x_5143_, v___f_5146_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_);
return v___x_5148_;
}
else
{
lean_object* v_a_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5156_; 
lean_dec_ref(v_eqs_5133_);
lean_dec_ref(v_eqvs_5132_);
lean_dec(v_numFields_5130_);
lean_dec(v_numParams_5129_);
lean_dec_ref(v_a_5128_);
lean_dec_ref(v___x_5127_);
lean_dec_ref(v___x_5124_);
lean_dec(v___x_5123_);
lean_dec(v___x_5122_);
lean_dec_ref(v___x_5121_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v___x_5118_);
lean_dec_ref(v___x_5117_);
lean_dec_ref(v___x_5116_);
lean_dec(v___x_5115_);
lean_dec(v___x_5114_);
lean_dec_ref(v_xs_5112_);
lean_dec_ref(v___x_5111_);
lean_dec_ref(v_P_5110_);
lean_dec(v_head_5109_);
v_a_5149_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5151_ = v___x_5139_;
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_a_5149_);
lean_dec(v___x_5139_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5156_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5154_; 
if (v_isShared_5152_ == 0)
{
v___x_5154_ = v___x_5151_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_head_5157_ = _args[0];
lean_object* v_P_5158_ = _args[1];
lean_object* v___x_5159_ = _args[2];
lean_object* v_xs_5160_ = _args[3];
lean_object* v_fields2_5161_ = _args[4];
lean_object* v___x_5162_ = _args[5];
lean_object* v___x_5163_ = _args[6];
lean_object* v___x_5164_ = _args[7];
lean_object* v___x_5165_ = _args[8];
lean_object* v___x_5166_ = _args[9];
lean_object* v___x_5167_ = _args[10];
lean_object* v___x_5168_ = _args[11];
lean_object* v___x_5169_ = _args[12];
lean_object* v___x_5170_ = _args[13];
lean_object* v___x_5171_ = _args[14];
lean_object* v___x_5172_ = _args[15];
lean_object* v_a_5173_ = _args[16];
lean_object* v_a_5174_ = _args[17];
lean_object* v___x_5175_ = _args[18];
lean_object* v_a_5176_ = _args[19];
lean_object* v_numParams_5177_ = _args[20];
lean_object* v_numFields_5178_ = _args[21];
lean_object* v___x_5179_ = _args[22];
lean_object* v_eqvs_5180_ = _args[23];
lean_object* v_eqs_5181_ = _args[24];
lean_object* v___y_5182_ = _args[25];
lean_object* v___y_5183_ = _args[26];
lean_object* v___y_5184_ = _args[27];
lean_object* v___y_5185_ = _args[28];
lean_object* v___y_5186_ = _args[29];
_start:
{
uint8_t v_a_18184__boxed_5187_; uint8_t v_a_18185__boxed_5188_; lean_object* v_res_5189_; 
v_a_18184__boxed_5187_ = lean_unbox(v_a_5173_);
v_a_18185__boxed_5188_ = lean_unbox(v_a_5174_);
v_res_5189_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1(v_head_5157_, v_P_5158_, v___x_5159_, v_xs_5160_, v_fields2_5161_, v___x_5162_, v___x_5163_, v___x_5164_, v___x_5165_, v___x_5166_, v___x_5167_, v___x_5168_, v___x_5169_, v___x_5170_, v___x_5171_, v___x_5172_, v_a_18184__boxed_5187_, v_a_18185__boxed_5188_, v___x_5175_, v_a_5176_, v_numParams_5177_, v_numFields_5178_, v___x_5179_, v_eqvs_5180_, v_eqs_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
lean_dec(v___y_5185_);
lean_dec_ref(v___y_5184_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec_ref(v_fields2_5161_);
return v_res_5189_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_5190_; lean_object* v_dummy_5191_; 
v___x_5190_ = lean_box(0);
v_dummy_5191_ = l_Lean_Expr_sort___override(v___x_5190_);
return v_dummy_5191_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2(lean_object* v___x_5192_, lean_object* v_val_5193_, lean_object* v___x_5194_, lean_object* v_head_5195_, lean_object* v_P_5196_, lean_object* v___x_5197_, lean_object* v_xs_5198_, lean_object* v_fields2_5199_, lean_object* v___x_5200_, lean_object* v___x_5201_, lean_object* v___x_5202_, lean_object* v___x_5203_, lean_object* v___x_5204_, lean_object* v___x_5205_, lean_object* v___x_5206_, uint8_t v_a_5207_, uint8_t v_a_5208_, lean_object* v___x_5209_, lean_object* v_a_5210_, lean_object* v_numParams_5211_, lean_object* v_numFields_5212_, lean_object* v___x_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_){
_start:
{
lean_object* v___x_5219_; 
lean_inc(v___y_5217_);
lean_inc_ref(v___y_5216_);
lean_inc(v___y_5215_);
lean_inc_ref(v___y_5214_);
lean_inc_ref(v___x_5192_);
v___x_5219_ = lean_infer_type(v___x_5192_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
if (lean_obj_tag(v___x_5219_) == 0)
{
lean_object* v_a_5220_; lean_object* v___x_5221_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_a_5220_);
lean_dec_ref_known(v___x_5219_, 1);
lean_inc(v___y_5217_);
lean_inc_ref(v___y_5216_);
lean_inc(v___y_5215_);
lean_inc_ref(v___y_5214_);
v___x_5221_ = lean_whnf(v_a_5220_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
if (lean_obj_tag(v___x_5221_) == 0)
{
lean_object* v_a_5222_; lean_object* v_numIndices_5223_; lean_object* v_dummy_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v_numIndices_5223_ = lean_ctor_get(v_val_5193_, 2);
lean_inc_n(v_numIndices_5223_, 3);
lean_dec_ref(v_val_5193_);
v_dummy_5224_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___closed__0);
v___x_5225_ = lean_mk_array(v_numIndices_5223_, v_dummy_5224_);
lean_inc_ref(v___x_5225_);
v___x_5226_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5223_, v_a_5222_, v___x_5225_);
lean_inc(v___y_5217_);
lean_inc_ref(v___y_5216_);
lean_inc(v___y_5215_);
lean_inc_ref(v___y_5214_);
lean_inc_ref(v___x_5194_);
v___x_5227_ = lean_infer_type(v___x_5194_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
lean_inc(v___y_5217_);
lean_inc_ref(v___y_5216_);
lean_inc(v___y_5215_);
lean_inc_ref(v___y_5214_);
v___x_5229_ = lean_whnf(v_a_5228_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
if (lean_obj_tag(v___x_5229_) == 0)
{
lean_object* v_a_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___f_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v_a_5230_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5230_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5231_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5223_, v_a_5230_, v___x_5225_);
v___x_5232_ = lean_box(v_a_5207_);
v___x_5233_ = lean_box(v_a_5208_);
lean_inc_ref(v___x_5194_);
lean_inc_ref(v___x_5231_);
lean_inc_ref(v___x_5192_);
lean_inc_ref(v___x_5226_);
v___f_5234_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__1___boxed), 30, 23);
lean_closure_set(v___f_5234_, 0, v_head_5195_);
lean_closure_set(v___f_5234_, 1, v_P_5196_);
lean_closure_set(v___f_5234_, 2, v___x_5197_);
lean_closure_set(v___f_5234_, 3, v_xs_5198_);
lean_closure_set(v___f_5234_, 4, v_fields2_5199_);
lean_closure_set(v___f_5234_, 5, v___x_5200_);
lean_closure_set(v___f_5234_, 6, v___x_5201_);
lean_closure_set(v___f_5234_, 7, v___x_5202_);
lean_closure_set(v___f_5234_, 8, v___x_5226_);
lean_closure_set(v___f_5234_, 9, v___x_5203_);
lean_closure_set(v___f_5234_, 10, v___x_5192_);
lean_closure_set(v___f_5234_, 11, v___x_5231_);
lean_closure_set(v___f_5234_, 12, v___x_5194_);
lean_closure_set(v___f_5234_, 13, v___x_5204_);
lean_closure_set(v___f_5234_, 14, v___x_5205_);
lean_closure_set(v___f_5234_, 15, v___x_5206_);
lean_closure_set(v___f_5234_, 16, v___x_5232_);
lean_closure_set(v___f_5234_, 17, v___x_5233_);
lean_closure_set(v___f_5234_, 18, v___x_5209_);
lean_closure_set(v___f_5234_, 19, v_a_5210_);
lean_closure_set(v___f_5234_, 20, v_numParams_5211_);
lean_closure_set(v___f_5234_, 21, v_numFields_5212_);
lean_closure_set(v___f_5234_, 22, v___x_5213_);
v___x_5235_ = lean_array_push(v___x_5226_, v___x_5192_);
v___x_5236_ = lean_array_push(v___x_5231_, v___x_5194_);
v___x_5237_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v___x_5235_, v___x_5236_, v___f_5234_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
return v___x_5237_;
}
else
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5245_; 
lean_dec_ref(v___x_5226_);
lean_dec_ref(v___x_5225_);
lean_dec(v_numIndices_5223_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v_numFields_5212_);
lean_dec(v_numParams_5211_);
lean_dec_ref(v_a_5210_);
lean_dec_ref(v___x_5209_);
lean_dec_ref(v___x_5206_);
lean_dec(v___x_5205_);
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v___x_5202_);
lean_dec(v___x_5201_);
lean_dec(v___x_5200_);
lean_dec_ref(v_fields2_5199_);
lean_dec_ref(v_xs_5198_);
lean_dec_ref(v___x_5197_);
lean_dec_ref(v_P_5196_);
lean_dec(v_head_5195_);
lean_dec_ref(v___x_5194_);
lean_dec_ref(v___x_5192_);
v_a_5238_ = lean_ctor_get(v___x_5229_, 0);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5229_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5240_ = v___x_5229_;
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___x_5229_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5245_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v___x_5243_; 
if (v_isShared_5241_ == 0)
{
v___x_5243_ = v___x_5240_;
goto v_reusejp_5242_;
}
else
{
lean_object* v_reuseFailAlloc_5244_; 
v_reuseFailAlloc_5244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5244_, 0, v_a_5238_);
v___x_5243_ = v_reuseFailAlloc_5244_;
goto v_reusejp_5242_;
}
v_reusejp_5242_:
{
return v___x_5243_;
}
}
}
}
else
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5253_; 
lean_dec_ref(v___x_5226_);
lean_dec_ref(v___x_5225_);
lean_dec(v_numIndices_5223_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v_numFields_5212_);
lean_dec(v_numParams_5211_);
lean_dec_ref(v_a_5210_);
lean_dec_ref(v___x_5209_);
lean_dec_ref(v___x_5206_);
lean_dec(v___x_5205_);
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v___x_5202_);
lean_dec(v___x_5201_);
lean_dec(v___x_5200_);
lean_dec_ref(v_fields2_5199_);
lean_dec_ref(v_xs_5198_);
lean_dec_ref(v___x_5197_);
lean_dec_ref(v_P_5196_);
lean_dec(v_head_5195_);
lean_dec_ref(v___x_5194_);
lean_dec_ref(v___x_5192_);
v_a_5246_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5248_ = v___x_5227_;
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___x_5227_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5253_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v___x_5251_; 
if (v_isShared_5249_ == 0)
{
v___x_5251_ = v___x_5248_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
}
}
else
{
lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v_numFields_5212_);
lean_dec(v_numParams_5211_);
lean_dec_ref(v_a_5210_);
lean_dec_ref(v___x_5209_);
lean_dec_ref(v___x_5206_);
lean_dec(v___x_5205_);
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v___x_5202_);
lean_dec(v___x_5201_);
lean_dec(v___x_5200_);
lean_dec_ref(v_fields2_5199_);
lean_dec_ref(v_xs_5198_);
lean_dec_ref(v___x_5197_);
lean_dec_ref(v_P_5196_);
lean_dec(v_head_5195_);
lean_dec_ref(v___x_5194_);
lean_dec_ref(v_val_5193_);
lean_dec_ref(v___x_5192_);
v_a_5254_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5221_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5221_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
else
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v_numFields_5212_);
lean_dec(v_numParams_5211_);
lean_dec_ref(v_a_5210_);
lean_dec_ref(v___x_5209_);
lean_dec_ref(v___x_5206_);
lean_dec(v___x_5205_);
lean_dec(v___x_5204_);
lean_dec_ref(v___x_5203_);
lean_dec_ref(v___x_5202_);
lean_dec(v___x_5201_);
lean_dec(v___x_5200_);
lean_dec_ref(v_fields2_5199_);
lean_dec_ref(v_xs_5198_);
lean_dec_ref(v___x_5197_);
lean_dec_ref(v_P_5196_);
lean_dec(v_head_5195_);
lean_dec_ref(v___x_5194_);
lean_dec_ref(v_val_5193_);
lean_dec_ref(v___x_5192_);
v_a_5262_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5219_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5219_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_5270_ = _args[0];
lean_object* v_val_5271_ = _args[1];
lean_object* v___x_5272_ = _args[2];
lean_object* v_head_5273_ = _args[3];
lean_object* v_P_5274_ = _args[4];
lean_object* v___x_5275_ = _args[5];
lean_object* v_xs_5276_ = _args[6];
lean_object* v_fields2_5277_ = _args[7];
lean_object* v___x_5278_ = _args[8];
lean_object* v___x_5279_ = _args[9];
lean_object* v___x_5280_ = _args[10];
lean_object* v___x_5281_ = _args[11];
lean_object* v___x_5282_ = _args[12];
lean_object* v___x_5283_ = _args[13];
lean_object* v___x_5284_ = _args[14];
lean_object* v_a_5285_ = _args[15];
lean_object* v_a_5286_ = _args[16];
lean_object* v___x_5287_ = _args[17];
lean_object* v_a_5288_ = _args[18];
lean_object* v_numParams_5289_ = _args[19];
lean_object* v_numFields_5290_ = _args[20];
lean_object* v___x_5291_ = _args[21];
lean_object* v___y_5292_ = _args[22];
lean_object* v___y_5293_ = _args[23];
lean_object* v___y_5294_ = _args[24];
lean_object* v___y_5295_ = _args[25];
lean_object* v___y_5296_ = _args[26];
_start:
{
uint8_t v_a_18291__boxed_5297_; uint8_t v_a_18292__boxed_5298_; lean_object* v_res_5299_; 
v_a_18291__boxed_5297_ = lean_unbox(v_a_5285_);
v_a_18292__boxed_5298_ = lean_unbox(v_a_5286_);
v_res_5299_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2(v___x_5270_, v_val_5271_, v___x_5272_, v_head_5273_, v_P_5274_, v___x_5275_, v_xs_5276_, v_fields2_5277_, v___x_5278_, v___x_5279_, v___x_5280_, v___x_5281_, v___x_5282_, v___x_5283_, v___x_5284_, v_a_18291__boxed_5297_, v_a_18292__boxed_5298_, v___x_5287_, v_a_5288_, v_numParams_5289_, v_numFields_5290_, v___x_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3(lean_object* v_P_5300_, lean_object* v_xs_5301_, lean_object* v_fields1_5302_, lean_object* v_head_5303_, lean_object* v_tail_5304_, lean_object* v_val_5305_, lean_object* v___x_5306_, lean_object* v___x_5307_, lean_object* v___x_5308_, uint8_t v_a_5309_, uint8_t v_a_5310_, lean_object* v___x_5311_, lean_object* v_a_5312_, lean_object* v_numParams_5313_, lean_object* v_numFields_5314_, lean_object* v___x_5315_, lean_object* v_fields2_5316_, lean_object* v_x_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___f_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; 
v___x_5323_ = lean_unsigned_to_nat(1u);
v___x_5324_ = lean_mk_empty_array_with_capacity(v___x_5323_);
lean_inc_ref(v_P_5300_);
lean_inc_ref(v___x_5324_);
v___x_5325_ = lean_array_push(v___x_5324_, v_P_5300_);
lean_inc_ref_n(v_xs_5301_, 3);
v___x_5326_ = l_Array_append___redArg(v_xs_5301_, v___x_5325_);
v___x_5327_ = l_Array_append___redArg(v___x_5326_, v_fields1_5302_);
v___x_5328_ = l_Array_append___redArg(v___x_5327_, v_fields2_5316_);
lean_inc(v_head_5303_);
v___x_5329_ = l_Lean_mkConst(v_head_5303_, v_tail_5304_);
v___x_5330_ = l_Array_append___redArg(v_xs_5301_, v_fields1_5302_);
lean_inc_ref(v___x_5329_);
v___x_5331_ = l_Lean_mkAppN(v___x_5329_, v___x_5330_);
v___x_5332_ = l_Array_append___redArg(v_xs_5301_, v_fields2_5316_);
v___x_5333_ = l_Lean_mkAppN(v___x_5329_, v___x_5332_);
lean_dec_ref(v___x_5332_);
v___x_5334_ = lean_box(v_a_5309_);
v___x_5335_ = lean_box(v_a_5310_);
lean_inc_ref(v___x_5328_);
lean_inc_ref(v_fields2_5316_);
v___f_5336_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__2___boxed), 27, 22);
lean_closure_set(v___f_5336_, 0, v___x_5331_);
lean_closure_set(v___f_5336_, 1, v_val_5305_);
lean_closure_set(v___f_5336_, 2, v___x_5333_);
lean_closure_set(v___f_5336_, 3, v_head_5303_);
lean_closure_set(v___f_5336_, 4, v_P_5300_);
lean_closure_set(v___f_5336_, 5, v___x_5330_);
lean_closure_set(v___f_5336_, 6, v_xs_5301_);
lean_closure_set(v___f_5336_, 7, v_fields2_5316_);
lean_closure_set(v___f_5336_, 8, v___x_5306_);
lean_closure_set(v___f_5336_, 9, v___x_5307_);
lean_closure_set(v___f_5336_, 10, v___x_5325_);
lean_closure_set(v___f_5336_, 11, v___x_5324_);
lean_closure_set(v___f_5336_, 12, v___x_5308_);
lean_closure_set(v___f_5336_, 13, v___x_5323_);
lean_closure_set(v___f_5336_, 14, v___x_5328_);
lean_closure_set(v___f_5336_, 15, v___x_5334_);
lean_closure_set(v___f_5336_, 16, v___x_5335_);
lean_closure_set(v___f_5336_, 17, v___x_5311_);
lean_closure_set(v___f_5336_, 18, v_a_5312_);
lean_closure_set(v___f_5336_, 19, v_numParams_5313_);
lean_closure_set(v___f_5336_, 20, v_numFields_5314_);
lean_closure_set(v___f_5336_, 21, v___x_5315_);
v___x_5337_ = lean_alloc_closure((void*)(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed), 8, 3);
lean_closure_set(v___x_5337_, 0, lean_box(0));
lean_closure_set(v___x_5337_, 1, v___x_5328_);
lean_closure_set(v___x_5337_, 2, v___f_5336_);
v___x_5338_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_fields2_5316_, v___x_5337_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_);
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_P_5339_ = _args[0];
lean_object* v_xs_5340_ = _args[1];
lean_object* v_fields1_5341_ = _args[2];
lean_object* v_head_5342_ = _args[3];
lean_object* v_tail_5343_ = _args[4];
lean_object* v_val_5344_ = _args[5];
lean_object* v___x_5345_ = _args[6];
lean_object* v___x_5346_ = _args[7];
lean_object* v___x_5347_ = _args[8];
lean_object* v_a_5348_ = _args[9];
lean_object* v_a_5349_ = _args[10];
lean_object* v___x_5350_ = _args[11];
lean_object* v_a_5351_ = _args[12];
lean_object* v_numParams_5352_ = _args[13];
lean_object* v_numFields_5353_ = _args[14];
lean_object* v___x_5354_ = _args[15];
lean_object* v_fields2_5355_ = _args[16];
lean_object* v_x_5356_ = _args[17];
lean_object* v___y_5357_ = _args[18];
lean_object* v___y_5358_ = _args[19];
lean_object* v___y_5359_ = _args[20];
lean_object* v___y_5360_ = _args[21];
lean_object* v___y_5361_ = _args[22];
_start:
{
uint8_t v_a_18450__boxed_5362_; uint8_t v_a_18451__boxed_5363_; lean_object* v_res_5364_; 
v_a_18450__boxed_5362_ = lean_unbox(v_a_5348_);
v_a_18451__boxed_5363_ = lean_unbox(v_a_5349_);
v_res_5364_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3(v_P_5339_, v_xs_5340_, v_fields1_5341_, v_head_5342_, v_tail_5343_, v_val_5344_, v___x_5345_, v___x_5346_, v___x_5347_, v_a_18450__boxed_5362_, v_a_18451__boxed_5363_, v___x_5350_, v_a_5351_, v_numParams_5352_, v_numFields_5353_, v___x_5354_, v_fields2_5355_, v_x_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
lean_dec(v___y_5360_);
lean_dec_ref(v___y_5359_);
lean_dec(v___y_5358_);
lean_dec_ref(v___y_5357_);
lean_dec_ref(v_x_5356_);
lean_dec_ref(v_fields1_5341_);
return v_res_5364_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4(lean_object* v_P_5365_, lean_object* v_xs_5366_, lean_object* v_head_5367_, lean_object* v_tail_5368_, lean_object* v_val_5369_, lean_object* v___x_5370_, lean_object* v___x_5371_, lean_object* v___x_5372_, uint8_t v_a_5373_, uint8_t v_a_5374_, lean_object* v___x_5375_, lean_object* v_a_5376_, lean_object* v_numParams_5377_, lean_object* v_numFields_5378_, lean_object* v___x_5379_, lean_object* v_t_5380_, lean_object* v___x_5381_, lean_object* v_fields1_5382_, lean_object* v_x_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___f_5391_; lean_object* v___x_5392_; 
v___x_5389_ = lean_box(v_a_5373_);
v___x_5390_ = lean_box(v_a_5374_);
v___f_5391_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__3___boxed), 23, 16);
lean_closure_set(v___f_5391_, 0, v_P_5365_);
lean_closure_set(v___f_5391_, 1, v_xs_5366_);
lean_closure_set(v___f_5391_, 2, v_fields1_5382_);
lean_closure_set(v___f_5391_, 3, v_head_5367_);
lean_closure_set(v___f_5391_, 4, v_tail_5368_);
lean_closure_set(v___f_5391_, 5, v_val_5369_);
lean_closure_set(v___f_5391_, 6, v___x_5370_);
lean_closure_set(v___f_5391_, 7, v___x_5371_);
lean_closure_set(v___f_5391_, 8, v___x_5372_);
lean_closure_set(v___f_5391_, 9, v___x_5389_);
lean_closure_set(v___f_5391_, 10, v___x_5390_);
lean_closure_set(v___f_5391_, 11, v___x_5375_);
lean_closure_set(v___f_5391_, 12, v_a_5376_);
lean_closure_set(v___f_5391_, 13, v_numParams_5377_);
lean_closure_set(v___f_5391_, 14, v_numFields_5378_);
lean_closure_set(v___f_5391_, 15, v___x_5379_);
v___x_5392_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5380_, v___x_5381_, v___f_5391_, v_a_5373_, v_a_5373_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_P_5393_ = _args[0];
lean_object* v_xs_5394_ = _args[1];
lean_object* v_head_5395_ = _args[2];
lean_object* v_tail_5396_ = _args[3];
lean_object* v_val_5397_ = _args[4];
lean_object* v___x_5398_ = _args[5];
lean_object* v___x_5399_ = _args[6];
lean_object* v___x_5400_ = _args[7];
lean_object* v_a_5401_ = _args[8];
lean_object* v_a_5402_ = _args[9];
lean_object* v___x_5403_ = _args[10];
lean_object* v_a_5404_ = _args[11];
lean_object* v_numParams_5405_ = _args[12];
lean_object* v_numFields_5406_ = _args[13];
lean_object* v___x_5407_ = _args[14];
lean_object* v_t_5408_ = _args[15];
lean_object* v___x_5409_ = _args[16];
lean_object* v_fields1_5410_ = _args[17];
lean_object* v_x_5411_ = _args[18];
lean_object* v___y_5412_ = _args[19];
lean_object* v___y_5413_ = _args[20];
lean_object* v___y_5414_ = _args[21];
lean_object* v___y_5415_ = _args[22];
lean_object* v___y_5416_ = _args[23];
_start:
{
uint8_t v_a_18533__boxed_5417_; uint8_t v_a_18534__boxed_5418_; lean_object* v_res_5419_; 
v_a_18533__boxed_5417_ = lean_unbox(v_a_5401_);
v_a_18534__boxed_5418_ = lean_unbox(v_a_5402_);
v_res_5419_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4(v_P_5393_, v_xs_5394_, v_head_5395_, v_tail_5396_, v_val_5397_, v___x_5398_, v___x_5399_, v___x_5400_, v_a_18533__boxed_5417_, v_a_18534__boxed_5418_, v___x_5403_, v_a_5404_, v_numParams_5405_, v_numFields_5406_, v___x_5407_, v_t_5408_, v___x_5409_, v_fields1_5410_, v_x_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
lean_dec(v___y_5415_);
lean_dec_ref(v___y_5414_);
lean_dec(v___y_5413_);
lean_dec_ref(v___y_5412_);
lean_dec_ref(v_x_5411_);
return v_res_5419_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5(lean_object* v_numFields_5420_, lean_object* v_xs_5421_, lean_object* v_head_5422_, lean_object* v_tail_5423_, lean_object* v_val_5424_, lean_object* v___x_5425_, lean_object* v___x_5426_, lean_object* v___x_5427_, uint8_t v_a_5428_, uint8_t v_a_5429_, lean_object* v___x_5430_, lean_object* v_a_5431_, lean_object* v_numParams_5432_, lean_object* v___x_5433_, lean_object* v_t_5434_, lean_object* v_P_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___f_5444_; lean_object* v___x_5445_; 
lean_inc(v_numFields_5420_);
v___x_5441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5441_, 0, v_numFields_5420_);
v___x_5442_ = lean_box(v_a_5428_);
v___x_5443_ = lean_box(v_a_5429_);
lean_inc_ref(v___x_5441_);
lean_inc_ref(v_t_5434_);
v___f_5444_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__4___boxed), 24, 17);
lean_closure_set(v___f_5444_, 0, v_P_5435_);
lean_closure_set(v___f_5444_, 1, v_xs_5421_);
lean_closure_set(v___f_5444_, 2, v_head_5422_);
lean_closure_set(v___f_5444_, 3, v_tail_5423_);
lean_closure_set(v___f_5444_, 4, v_val_5424_);
lean_closure_set(v___f_5444_, 5, v___x_5425_);
lean_closure_set(v___f_5444_, 6, v___x_5426_);
lean_closure_set(v___f_5444_, 7, v___x_5427_);
lean_closure_set(v___f_5444_, 8, v___x_5442_);
lean_closure_set(v___f_5444_, 9, v___x_5443_);
lean_closure_set(v___f_5444_, 10, v___x_5430_);
lean_closure_set(v___f_5444_, 11, v_a_5431_);
lean_closure_set(v___f_5444_, 12, v_numParams_5432_);
lean_closure_set(v___f_5444_, 13, v_numFields_5420_);
lean_closure_set(v___f_5444_, 14, v___x_5433_);
lean_closure_set(v___f_5444_, 15, v_t_5434_);
lean_closure_set(v___f_5444_, 16, v___x_5441_);
v___x_5445_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5434_, v___x_5441_, v___f_5444_, v_a_5428_, v_a_5428_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_);
return v___x_5445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_numFields_5446_ = _args[0];
lean_object* v_xs_5447_ = _args[1];
lean_object* v_head_5448_ = _args[2];
lean_object* v_tail_5449_ = _args[3];
lean_object* v_val_5450_ = _args[4];
lean_object* v___x_5451_ = _args[5];
lean_object* v___x_5452_ = _args[6];
lean_object* v___x_5453_ = _args[7];
lean_object* v_a_5454_ = _args[8];
lean_object* v_a_5455_ = _args[9];
lean_object* v___x_5456_ = _args[10];
lean_object* v_a_5457_ = _args[11];
lean_object* v_numParams_5458_ = _args[12];
lean_object* v___x_5459_ = _args[13];
lean_object* v_t_5460_ = _args[14];
lean_object* v_P_5461_ = _args[15];
lean_object* v___y_5462_ = _args[16];
lean_object* v___y_5463_ = _args[17];
lean_object* v___y_5464_ = _args[18];
lean_object* v___y_5465_ = _args[19];
lean_object* v___y_5466_ = _args[20];
_start:
{
uint8_t v_a_18595__boxed_5467_; uint8_t v_a_18596__boxed_5468_; lean_object* v_res_5469_; 
v_a_18595__boxed_5467_ = lean_unbox(v_a_5454_);
v_a_18596__boxed_5468_ = lean_unbox(v_a_5455_);
v_res_5469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5(v_numFields_5446_, v_xs_5447_, v_head_5448_, v_tail_5449_, v_val_5450_, v___x_5451_, v___x_5452_, v___x_5453_, v_a_18595__boxed_5467_, v_a_18596__boxed_5468_, v___x_5456_, v_a_5457_, v_numParams_5458_, v___x_5459_, v_t_5460_, v_P_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
return v_res_5469_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6(lean_object* v_numFields_5470_, lean_object* v_head_5471_, lean_object* v_tail_5472_, lean_object* v_val_5473_, lean_object* v___x_5474_, lean_object* v___x_5475_, lean_object* v___x_5476_, uint8_t v_a_5477_, uint8_t v_a_5478_, lean_object* v___x_5479_, lean_object* v_a_5480_, lean_object* v_numParams_5481_, lean_object* v___x_5482_, lean_object* v_head_5483_, lean_object* v_xs_5484_, lean_object* v_t_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_){
_start:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___f_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; 
v___x_5491_ = lean_box(v_a_5477_);
v___x_5492_ = lean_box(v_a_5478_);
v___f_5493_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__5___boxed), 21, 15);
lean_closure_set(v___f_5493_, 0, v_numFields_5470_);
lean_closure_set(v___f_5493_, 1, v_xs_5484_);
lean_closure_set(v___f_5493_, 2, v_head_5471_);
lean_closure_set(v___f_5493_, 3, v_tail_5472_);
lean_closure_set(v___f_5493_, 4, v_val_5473_);
lean_closure_set(v___f_5493_, 5, v___x_5474_);
lean_closure_set(v___f_5493_, 6, v___x_5475_);
lean_closure_set(v___f_5493_, 7, v___x_5476_);
lean_closure_set(v___f_5493_, 8, v___x_5491_);
lean_closure_set(v___f_5493_, 9, v___x_5492_);
lean_closure_set(v___f_5493_, 10, v___x_5479_);
lean_closure_set(v___f_5493_, 11, v_a_5480_);
lean_closure_set(v___f_5493_, 12, v_numParams_5481_);
lean_closure_set(v___f_5493_, 13, v___x_5482_);
lean_closure_set(v___f_5493_, 14, v_t_5485_);
v___x_5494_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_5495_ = l_Lean_Expr_sort___override(v_head_5483_);
v___x_5496_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5494_, v___x_5495_, v___f_5493_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_numFields_5497_ = _args[0];
lean_object* v_head_5498_ = _args[1];
lean_object* v_tail_5499_ = _args[2];
lean_object* v_val_5500_ = _args[3];
lean_object* v___x_5501_ = _args[4];
lean_object* v___x_5502_ = _args[5];
lean_object* v___x_5503_ = _args[6];
lean_object* v_a_5504_ = _args[7];
lean_object* v_a_5505_ = _args[8];
lean_object* v___x_5506_ = _args[9];
lean_object* v_a_5507_ = _args[10];
lean_object* v_numParams_5508_ = _args[11];
lean_object* v___x_5509_ = _args[12];
lean_object* v_head_5510_ = _args[13];
lean_object* v_xs_5511_ = _args[14];
lean_object* v_t_5512_ = _args[15];
lean_object* v___y_5513_ = _args[16];
lean_object* v___y_5514_ = _args[17];
lean_object* v___y_5515_ = _args[18];
lean_object* v___y_5516_ = _args[19];
lean_object* v___y_5517_ = _args[20];
_start:
{
uint8_t v_a_18656__boxed_5518_; uint8_t v_a_18657__boxed_5519_; lean_object* v_res_5520_; 
v_a_18656__boxed_5518_ = lean_unbox(v_a_5504_);
v_a_18657__boxed_5519_ = lean_unbox(v_a_5505_);
v_res_5520_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6(v_numFields_5497_, v_head_5498_, v_tail_5499_, v_val_5500_, v___x_5501_, v___x_5502_, v___x_5503_, v_a_18656__boxed_5518_, v_a_18657__boxed_5519_, v___x_5506_, v_a_5507_, v_numParams_5508_, v___x_5509_, v_head_5510_, v_xs_5511_, v_t_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg(lean_object* v_tail_5521_, lean_object* v_val_5522_, lean_object* v___x_5523_, lean_object* v___x_5524_, uint8_t v_a_5525_, uint8_t v_a_5526_, lean_object* v_a_5527_, lean_object* v_head_5528_, lean_object* v_as_x27_5529_, lean_object* v_b_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_){
_start:
{
if (lean_obj_tag(v_as_x27_5529_) == 0)
{
lean_object* v___x_5536_; 
lean_dec(v_head_5528_);
lean_dec_ref(v_a_5527_);
lean_dec(v___x_5524_);
lean_dec(v___x_5523_);
lean_dec_ref(v_val_5522_);
lean_dec(v_tail_5521_);
v___x_5536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5536_, 0, v_b_5530_);
return v___x_5536_;
}
else
{
lean_object* v_head_5537_; lean_object* v_tail_5538_; lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; 
v_head_5537_ = lean_ctor_get(v_as_x27_5529_, 0);
v_tail_5538_ = lean_ctor_get(v_as_x27_5529_, 1);
v___x_5539_ = lean_box(0);
v___x_5540_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
lean_inc(v_head_5537_);
v___x_5541_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_head_5537_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
if (lean_obj_tag(v___x_5541_) == 0)
{
lean_object* v_a_5542_; lean_object* v_toConstantVal_5543_; lean_object* v_numParams_5544_; lean_object* v_numFields_5545_; lean_object* v___x_5546_; uint8_t v___x_5547_; 
v_a_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_a_5542_);
lean_dec_ref_known(v___x_5541_, 1);
v_toConstantVal_5543_ = lean_ctor_get(v_a_5542_, 0);
lean_inc_ref(v_toConstantVal_5543_);
v_numParams_5544_ = lean_ctor_get(v_a_5542_, 3);
lean_inc(v_numParams_5544_);
v_numFields_5545_ = lean_ctor_get(v_a_5542_, 4);
lean_inc(v_numFields_5545_);
lean_dec(v_a_5542_);
v___x_5546_ = lean_unsigned_to_nat(0u);
v___x_5547_ = lean_nat_dec_lt(v___x_5546_, v_numFields_5545_);
if (v___x_5547_ == 0)
{
lean_dec(v_numFields_5545_);
lean_dec(v_numParams_5544_);
lean_dec_ref(v_toConstantVal_5543_);
v_as_x27_5529_ = v_tail_5538_;
v_b_5530_ = v___x_5539_;
goto _start;
}
else
{
lean_object* v_type_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___f_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v_type_5549_ = lean_ctor_get(v_toConstantVal_5543_, 2);
lean_inc_ref(v_type_5549_);
lean_dec_ref(v_toConstantVal_5543_);
v___x_5550_ = lean_box(v_a_5525_);
v___x_5551_ = lean_box(v_a_5526_);
lean_inc(v_head_5528_);
lean_inc(v_numParams_5544_);
lean_inc_ref(v_a_5527_);
lean_inc(v___x_5524_);
lean_inc(v___x_5523_);
lean_inc_ref(v_val_5522_);
lean_inc(v_tail_5521_);
lean_inc(v_head_5537_);
v___f_5552_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___lam__6___boxed), 21, 14);
lean_closure_set(v___f_5552_, 0, v_numFields_5545_);
lean_closure_set(v___f_5552_, 1, v_head_5537_);
lean_closure_set(v___f_5552_, 2, v_tail_5521_);
lean_closure_set(v___f_5552_, 3, v_val_5522_);
lean_closure_set(v___f_5552_, 4, v___x_5523_);
lean_closure_set(v___f_5552_, 5, v___x_5524_);
lean_closure_set(v___f_5552_, 6, v___x_5546_);
lean_closure_set(v___f_5552_, 7, v___x_5550_);
lean_closure_set(v___f_5552_, 8, v___x_5551_);
lean_closure_set(v___f_5552_, 9, v___x_5540_);
lean_closure_set(v___f_5552_, 10, v_a_5527_);
lean_closure_set(v___f_5552_, 11, v_numParams_5544_);
lean_closure_set(v___f_5552_, 12, v___x_5539_);
lean_closure_set(v___f_5552_, 13, v_head_5528_);
v___x_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5553_, 0, v_numParams_5544_);
v___x_5554_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_5549_, v___x_5553_, v___f_5552_, v_a_5525_, v_a_5525_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
if (lean_obj_tag(v___x_5554_) == 0)
{
lean_dec_ref_known(v___x_5554_, 1);
v_as_x27_5529_ = v_tail_5538_;
v_b_5530_ = v___x_5539_;
goto _start;
}
else
{
lean_dec(v_head_5528_);
lean_dec_ref(v_a_5527_);
lean_dec(v___x_5524_);
lean_dec(v___x_5523_);
lean_dec_ref(v_val_5522_);
lean_dec(v_tail_5521_);
return v___x_5554_;
}
}
}
else
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
lean_dec(v_head_5528_);
lean_dec_ref(v_a_5527_);
lean_dec(v___x_5524_);
lean_dec(v___x_5523_);
lean_dec_ref(v_val_5522_);
lean_dec(v_tail_5521_);
v_a_5556_ = lean_ctor_get(v___x_5541_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5563_ == 0)
{
v___x_5558_ = v___x_5541_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v___x_5541_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
if (v_isShared_5559_ == 0)
{
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5556_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg___boxed(lean_object* v_tail_5564_, lean_object* v_val_5565_, lean_object* v___x_5566_, lean_object* v___x_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_, lean_object* v_head_5571_, lean_object* v_as_x27_5572_, lean_object* v_b_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
uint8_t v_a_18719__boxed_5579_; uint8_t v_a_18720__boxed_5580_; lean_object* v_res_5581_; 
v_a_18719__boxed_5579_ = lean_unbox(v_a_5568_);
v_a_18720__boxed_5580_ = lean_unbox(v_a_5569_);
v_res_5581_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg(v_tail_5564_, v_val_5565_, v___x_5566_, v___x_5567_, v_a_18719__boxed_5579_, v_a_18720__boxed_5580_, v_a_5570_, v_head_5571_, v_as_x27_5572_, v_b_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
lean_dec(v_as_x27_5572_);
return v_res_5581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1(void){
_start:
{
lean_object* v___x_5583_; lean_object* v___x_5584_; 
v___x_5583_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0));
v___x_5584_ = l_Lean_stringToMessageData(v___x_5583_);
return v___x_5584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(lean_object* v_declName_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_, lean_object* v_a_5589_){
_start:
{
lean_object* v___x_5591_; 
lean_inc(v_declName_5585_);
v___x_5591_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
if (lean_obj_tag(v___x_5591_) == 0)
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5677_; 
v_a_5592_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5594_ = v___x_5591_;
v_isShared_5595_ = v_isSharedCheck_5677_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5591_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5677_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
if (lean_obj_tag(v_a_5592_) == 5)
{
lean_object* v_val_5596_; lean_object* v___x_5597_; 
lean_del_object(v___x_5594_);
v_val_5596_ = lean_ctor_get(v_a_5592_, 0);
lean_inc_ref(v_val_5596_);
lean_dec_ref_known(v_a_5592_, 1);
lean_inc(v_declName_5585_);
v___x_5597_ = l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(v_declName_5585_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5664_; 
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5664_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5664_ == 0)
{
v___x_5600_ = v___x_5597_;
v_isShared_5601_ = v_isSharedCheck_5664_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5597_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5664_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
uint8_t v___x_5602_; 
v___x_5602_ = lean_unbox(v_a_5598_);
if (v___x_5602_ == 0)
{
lean_object* v___x_5603_; lean_object* v___x_5605_; 
lean_dec(v_a_5598_);
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v___x_5603_ = lean_box(0);
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 0, v___x_5603_);
v___x_5605_ = v___x_5600_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v___x_5603_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
else
{
lean_object* v_toConstantVal_5607_; lean_object* v_ctors_5608_; lean_object* v_type_5609_; lean_object* v___x_5610_; 
lean_del_object(v___x_5600_);
v_toConstantVal_5607_ = lean_ctor_get(v_val_5596_, 0);
v_ctors_5608_ = lean_ctor_get(v_val_5596_, 4);
lean_inc(v_ctors_5608_);
v_type_5609_ = lean_ctor_get(v_toConstantVal_5607_, 2);
lean_inc_ref(v_type_5609_);
v___x_5610_ = l_Lean_Meta_isPropFormerType(v_type_5609_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
if (lean_obj_tag(v___x_5610_) == 0)
{
lean_object* v_a_5611_; lean_object* v___x_5613_; uint8_t v_isShared_5614_; uint8_t v_isSharedCheck_5655_; 
v_a_5611_ = lean_ctor_get(v___x_5610_, 0);
v_isSharedCheck_5655_ = !lean_is_exclusive(v___x_5610_);
if (v_isSharedCheck_5655_ == 0)
{
v___x_5613_ = v___x_5610_;
v_isShared_5614_ = v_isSharedCheck_5655_;
goto v_resetjp_5612_;
}
else
{
lean_inc(v_a_5611_);
lean_dec(v___x_5610_);
v___x_5613_ = lean_box(0);
v_isShared_5614_ = v_isSharedCheck_5655_;
goto v_resetjp_5612_;
}
v_resetjp_5612_:
{
uint8_t v___x_5615_; 
v___x_5615_ = lean_unbox(v_a_5611_);
if (v___x_5615_ == 0)
{
lean_object* v___x_5616_; lean_object* v___x_5617_; 
lean_del_object(v___x_5613_);
lean_inc(v_declName_5585_);
v___x_5616_ = l_Lean_mkRecName(v_declName_5585_);
v___x_5617_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_5616_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5618_);
lean_dec_ref_known(v___x_5617_, 1);
v___x_5619_ = l_Lean_ConstantInfo_levelParams(v_a_5618_);
v___x_5620_ = lean_box(0);
v___x_5621_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v___x_5619_, v___x_5620_);
if (lean_obj_tag(v___x_5621_) == 1)
{
lean_object* v_head_5622_; lean_object* v_tail_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; uint8_t v___x_5627_; uint8_t v___x_5628_; lean_object* v___x_5629_; 
v_head_5622_ = lean_ctor_get(v___x_5621_, 0);
lean_inc(v_head_5622_);
v_tail_5623_ = lean_ctor_get(v___x_5621_, 1);
lean_inc(v_tail_5623_);
v___x_5624_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_5625_ = l_Lean_Name_str___override(v_declName_5585_, v___x_5624_);
v___x_5626_ = lean_box(0);
v___x_5627_ = lean_unbox(v_a_5611_);
lean_dec(v_a_5611_);
v___x_5628_ = lean_unbox(v_a_5598_);
lean_dec(v_a_5598_);
v___x_5629_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg(v_tail_5623_, v_val_5596_, v___x_5625_, v___x_5621_, v___x_5627_, v___x_5628_, v_a_5618_, v_head_5622_, v_ctors_5608_, v___x_5626_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
lean_dec(v_ctors_5608_);
if (lean_obj_tag(v___x_5629_) == 0)
{
lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5629_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; 
v_unused_5637_ = lean_ctor_get(v___x_5629_, 0);
lean_dec(v_unused_5637_);
v___x_5631_ = v___x_5629_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_dec(v___x_5629_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
lean_ctor_set(v___x_5631_, 0, v___x_5626_);
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v___x_5626_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
else
{
return v___x_5629_;
}
}
else
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
lean_dec(v___x_5621_);
lean_dec(v_a_5611_);
lean_dec(v_ctors_5608_);
lean_dec(v_a_5598_);
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v___x_5638_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1);
v___x_5639_ = l_Lean_ConstantInfo_name(v_a_5618_);
lean_dec(v_a_5618_);
v___x_5640_ = l_Lean_MessageData_ofName(v___x_5639_);
v___x_5641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5641_, 0, v___x_5638_);
lean_ctor_set(v___x_5641_, 1, v___x_5640_);
v___x_5642_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_5641_, v_a_5586_, v_a_5587_, v_a_5588_, v_a_5589_);
return v___x_5642_;
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec(v_a_5611_);
lean_dec(v_ctors_5608_);
lean_dec(v_a_5598_);
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v_a_5643_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5617_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5617_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
else
{
lean_object* v___x_5651_; lean_object* v___x_5653_; 
lean_dec(v_a_5611_);
lean_dec(v_ctors_5608_);
lean_dec(v_a_5598_);
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v___x_5651_ = lean_box(0);
if (v_isShared_5614_ == 0)
{
lean_ctor_set(v___x_5613_, 0, v___x_5651_);
v___x_5653_ = v___x_5613_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v___x_5651_);
v___x_5653_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
return v___x_5653_;
}
}
}
}
else
{
lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_dec(v_ctors_5608_);
lean_dec(v_a_5598_);
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v_a_5656_ = lean_ctor_get(v___x_5610_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5610_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5610_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5610_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
}
}
}
else
{
lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5672_; 
lean_dec_ref(v_val_5596_);
lean_dec(v_declName_5585_);
v_a_5665_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5672_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5667_ = v___x_5597_;
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_dec(v___x_5597_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5670_; 
if (v_isShared_5668_ == 0)
{
v___x_5670_ = v___x_5667_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_a_5665_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
else
{
lean_object* v___x_5673_; lean_object* v___x_5675_; 
lean_dec(v_a_5592_);
lean_dec(v_declName_5585_);
v___x_5673_ = lean_box(0);
if (v_isShared_5595_ == 0)
{
lean_ctor_set(v___x_5594_, 0, v___x_5673_);
v___x_5675_ = v___x_5594_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5673_);
v___x_5675_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
return v___x_5675_;
}
}
}
}
else
{
lean_object* v_a_5678_; lean_object* v___x_5680_; uint8_t v_isShared_5681_; uint8_t v_isSharedCheck_5685_; 
lean_dec(v_declName_5585_);
v_a_5678_ = lean_ctor_get(v___x_5591_, 0);
v_isSharedCheck_5685_ = !lean_is_exclusive(v___x_5591_);
if (v_isSharedCheck_5685_ == 0)
{
v___x_5680_ = v___x_5591_;
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
else
{
lean_inc(v_a_5678_);
lean_dec(v___x_5591_);
v___x_5680_ = lean_box(0);
v_isShared_5681_ = v_isSharedCheck_5685_;
goto v_resetjp_5679_;
}
v_resetjp_5679_:
{
lean_object* v___x_5683_; 
if (v_isShared_5681_ == 0)
{
v___x_5683_ = v___x_5680_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5684_; 
v_reuseFailAlloc_5684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
v___x_5683_ = v_reuseFailAlloc_5684_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
return v___x_5683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___boxed(lean_object* v_declName_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v_res_5692_; 
v_res_5692_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_);
lean_dec(v_a_5690_);
lean_dec_ref(v_a_5689_);
lean_dec(v_a_5688_);
lean_dec_ref(v_a_5687_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(lean_object* v_range_5693_, lean_object* v_b_5694_, lean_object* v_i_5695_, lean_object* v_hs_5696_, lean_object* v_hl_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
lean_object* v___x_5703_; 
v___x_5703_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___redArg(v_range_5693_, v_b_5694_, v_i_5695_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___boxed(lean_object* v_range_5704_, lean_object* v_b_5705_, lean_object* v_i_5706_, lean_object* v_hs_5707_, lean_object* v_hl_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_){
_start:
{
lean_object* v_res_5714_; 
v_res_5714_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(v_range_5704_, v_b_5705_, v_i_5706_, v_hs_5707_, v_hl_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec_ref(v_range_5704_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3(lean_object* v_tail_5715_, lean_object* v_val_5716_, lean_object* v___x_5717_, lean_object* v___x_5718_, uint8_t v_a_5719_, uint8_t v_a_5720_, lean_object* v_a_5721_, lean_object* v_head_5722_, lean_object* v_as_5723_, lean_object* v_as_x27_5724_, lean_object* v_b_5725_, lean_object* v_a_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
lean_object* v___x_5732_; 
v___x_5732_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___redArg(v_tail_5715_, v_val_5716_, v___x_5717_, v___x_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_head_5722_, v_as_x27_5724_, v_b_5725_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_);
return v___x_5732_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3___boxed(lean_object** _args){
lean_object* v_tail_5733_ = _args[0];
lean_object* v_val_5734_ = _args[1];
lean_object* v___x_5735_ = _args[2];
lean_object* v___x_5736_ = _args[3];
lean_object* v_a_5737_ = _args[4];
lean_object* v_a_5738_ = _args[5];
lean_object* v_a_5739_ = _args[6];
lean_object* v_head_5740_ = _args[7];
lean_object* v_as_5741_ = _args[8];
lean_object* v_as_x27_5742_ = _args[9];
lean_object* v_b_5743_ = _args[10];
lean_object* v_a_5744_ = _args[11];
lean_object* v___y_5745_ = _args[12];
lean_object* v___y_5746_ = _args[13];
lean_object* v___y_5747_ = _args[14];
lean_object* v___y_5748_ = _args[15];
lean_object* v___y_5749_ = _args[16];
_start:
{
uint8_t v_a_19024__boxed_5750_; uint8_t v_a_19025__boxed_5751_; lean_object* v_res_5752_; 
v_a_19024__boxed_5750_ = lean_unbox(v_a_5737_);
v_a_19025__boxed_5751_ = lean_unbox(v_a_5738_);
v_res_5752_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__3(v_tail_5733_, v_val_5734_, v___x_5735_, v___x_5736_, v_a_19024__boxed_5750_, v_a_19025__boxed_5751_, v_a_5739_, v_head_5740_, v_as_5741_, v_as_x27_5742_, v_b_5743_, v_a_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_);
lean_dec(v___y_5748_);
lean_dec_ref(v___y_5747_);
lean_dec(v___y_5746_);
lean_dec_ref(v___y_5745_);
lean_dec(v_as_x27_5742_);
lean_dec(v_as_5741_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(lean_object* v_declName_5753_, lean_object* v_a_5754_, lean_object* v_a_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_){
_start:
{
lean_object* v___x_5759_; 
lean_inc(v_declName_5753_);
v___x_5759_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
if (lean_obj_tag(v___x_5759_) == 0)
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5812_; 
v_a_5760_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5762_ = v___x_5759_;
v_isShared_5763_ = v_isSharedCheck_5812_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5759_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5812_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
if (lean_obj_tag(v_a_5760_) == 5)
{
lean_object* v_val_5764_; lean_object* v___x_5765_; 
lean_del_object(v___x_5762_);
v_val_5764_ = lean_ctor_get(v_a_5760_, 0);
lean_inc_ref(v_val_5764_);
lean_dec_ref_known(v_a_5760_, 1);
lean_inc(v_declName_5753_);
v___x_5765_ = l_Lean_isLargeEliminating___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(v_declName_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5766_; lean_object* v___x_5768_; uint8_t v_isShared_5769_; uint8_t v_isSharedCheck_5799_; 
v_a_5766_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5799_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5768_ = v___x_5765_;
v_isShared_5769_ = v_isSharedCheck_5799_;
goto v_resetjp_5767_;
}
else
{
lean_inc(v_a_5766_);
lean_dec(v___x_5765_);
v___x_5768_ = lean_box(0);
v_isShared_5769_ = v_isSharedCheck_5799_;
goto v_resetjp_5767_;
}
v_resetjp_5767_:
{
uint8_t v___x_5770_; 
v___x_5770_ = lean_unbox(v_a_5766_);
lean_dec(v_a_5766_);
if (v___x_5770_ == 0)
{
lean_object* v___x_5771_; lean_object* v___x_5773_; 
lean_dec_ref(v_val_5764_);
lean_dec(v_declName_5753_);
v___x_5771_ = lean_box(0);
if (v_isShared_5769_ == 0)
{
lean_ctor_set(v___x_5768_, 0, v___x_5771_);
v___x_5773_ = v___x_5768_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5771_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
else
{
lean_object* v_toConstantVal_5775_; lean_object* v_type_5776_; lean_object* v___x_5777_; 
lean_del_object(v___x_5768_);
v_toConstantVal_5775_ = lean_ctor_get(v_val_5764_, 0);
lean_inc_ref(v_toConstantVal_5775_);
lean_dec_ref(v_val_5764_);
v_type_5776_ = lean_ctor_get(v_toConstantVal_5775_, 2);
lean_inc_ref(v_type_5776_);
lean_dec_ref(v_toConstantVal_5775_);
v___x_5777_ = l_Lean_Meta_isPropFormerType(v_type_5776_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5790_; 
v_a_5778_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5780_ = v___x_5777_;
v_isShared_5781_ = v_isSharedCheck_5790_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5777_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5790_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
uint8_t v___x_5782_; 
v___x_5782_ = lean_unbox(v_a_5778_);
lean_dec(v_a_5778_);
if (v___x_5782_ == 0)
{
lean_object* v___x_5783_; 
lean_del_object(v___x_5780_);
lean_inc(v_declName_5753_);
v___x_5783_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_declName_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v___x_5784_; 
lean_dec_ref_known(v___x_5783_, 1);
lean_inc(v_declName_5753_);
v___x_5784_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(v_declName_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
if (lean_obj_tag(v___x_5784_) == 0)
{
lean_object* v___x_5785_; 
lean_dec_ref_known(v___x_5784_, 1);
v___x_5785_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_);
return v___x_5785_;
}
else
{
lean_dec(v_declName_5753_);
return v___x_5784_;
}
}
else
{
lean_dec(v_declName_5753_);
return v___x_5783_;
}
}
else
{
lean_object* v___x_5786_; lean_object* v___x_5788_; 
lean_dec(v_declName_5753_);
v___x_5786_ = lean_box(0);
if (v_isShared_5781_ == 0)
{
lean_ctor_set(v___x_5780_, 0, v___x_5786_);
v___x_5788_ = v___x_5780_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v___x_5786_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
}
}
else
{
lean_object* v_a_5791_; lean_object* v___x_5793_; uint8_t v_isShared_5794_; uint8_t v_isSharedCheck_5798_; 
lean_dec(v_declName_5753_);
v_a_5791_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5793_ = v___x_5777_;
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
else
{
lean_inc(v_a_5791_);
lean_dec(v___x_5777_);
v___x_5793_ = lean_box(0);
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
v_resetjp_5792_:
{
lean_object* v___x_5796_; 
if (v_isShared_5794_ == 0)
{
v___x_5796_ = v___x_5793_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
}
}
else
{
lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5807_; 
lean_dec_ref(v_val_5764_);
lean_dec(v_declName_5753_);
v_a_5800_ = lean_ctor_get(v___x_5765_, 0);
v_isSharedCheck_5807_ = !lean_is_exclusive(v___x_5765_);
if (v_isSharedCheck_5807_ == 0)
{
v___x_5802_ = v___x_5765_;
v_isShared_5803_ = v_isSharedCheck_5807_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5765_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5807_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v___x_5805_; 
if (v_isShared_5803_ == 0)
{
v___x_5805_ = v___x_5802_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
v___x_5805_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
return v___x_5805_;
}
}
}
}
else
{
lean_object* v___x_5808_; lean_object* v___x_5810_; 
lean_dec(v_a_5760_);
lean_dec(v_declName_5753_);
v___x_5808_ = lean_box(0);
if (v_isShared_5763_ == 0)
{
lean_ctor_set(v___x_5762_, 0, v___x_5808_);
v___x_5810_ = v___x_5762_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5808_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
}
}
else
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5820_; 
lean_dec(v_declName_5753_);
v_a_5813_ = lean_ctor_get(v___x_5759_, 0);
v_isSharedCheck_5820_ = !lean_is_exclusive(v___x_5759_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5815_ = v___x_5759_;
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5759_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5818_; 
if (v_isShared_5816_ == 0)
{
v___x_5818_ = v___x_5815_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_a_5813_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore___boxed(lean_object* v_declName_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_){
_start:
{
lean_object* v_res_5827_; 
v_res_5827_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_);
lean_dec(v_a_5825_);
lean_dec_ref(v_a_5824_);
lean_dec(v_a_5823_);
lean_dec_ref(v_a_5822_);
return v_res_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(lean_object* v_P_5831_, lean_object* v_x_5832_, lean_object* v___x_5833_, lean_object* v_enumName_5834_, lean_object* v_a_5835_, lean_object* v_levelParams_5836_, lean_object* v_val_5837_, lean_object* v___x_5838_, lean_object* v_y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; uint8_t v___x_5850_; uint8_t v___x_5851_; uint8_t v___x_5852_; lean_object* v___x_5853_; 
v___x_5845_ = lean_unsigned_to_nat(3u);
v___x_5846_ = lean_mk_empty_array_with_capacity(v___x_5845_);
lean_inc_ref(v_P_5831_);
v___x_5847_ = lean_array_push(v___x_5846_, v_P_5831_);
lean_inc_ref(v_x_5832_);
v___x_5848_ = lean_array_push(v___x_5847_, v_x_5832_);
lean_inc_ref(v_y_5839_);
v___x_5849_ = lean_array_push(v___x_5848_, v_y_5839_);
v___x_5850_ = 0;
v___x_5851_ = 1;
v___x_5852_ = 1;
v___x_5853_ = l_Lean_Meta_mkForallFVars(v___x_5849_, v___x_5833_, v___x_5850_, v___x_5851_, v___x_5851_, v___x_5852_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5853_) == 0)
{
lean_object* v_a_5854_; lean_object* v_declValue_5856_; lean_object* v___y_5857_; lean_object* v___y_5858_; lean_object* v___y_5859_; lean_object* v___y_5860_; lean_object* v___x_5873_; lean_object* v___x_5874_; uint8_t v___x_5875_; 
v_a_5854_ = lean_ctor_get(v___x_5853_, 0);
lean_inc(v_a_5854_);
lean_dec_ref_known(v___x_5853_, 1);
v___x_5873_ = l_Lean_InductiveVal_numCtors(v_val_5837_);
v___x_5874_ = lean_unsigned_to_nat(1u);
v___x_5875_ = lean_nat_dec_eq(v___x_5873_, v___x_5874_);
lean_dec(v___x_5873_);
if (v___x_5875_ == 0)
{
lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; 
lean_inc(v_enumName_5834_);
v___x_5876_ = l_Lean_mkCtorIdxName(v_enumName_5834_);
v___x_5877_ = l_Lean_mkConst(v___x_5876_, v___x_5838_);
v___x_5878_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1));
v___x_5879_ = lean_unsigned_to_nat(4u);
v___x_5880_ = lean_mk_empty_array_with_capacity(v___x_5879_);
v___x_5881_ = lean_array_push(v___x_5880_, v___x_5877_);
v___x_5882_ = lean_array_push(v___x_5881_, v_P_5831_);
v___x_5883_ = lean_array_push(v___x_5882_, v_x_5832_);
v___x_5884_ = lean_array_push(v___x_5883_, v_y_5839_);
v___x_5885_ = l_Lean_Meta_mkAppM(v___x_5878_, v___x_5884_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5885_) == 0)
{
lean_object* v_a_5886_; lean_object* v___x_5887_; 
v_a_5886_ = lean_ctor_get(v___x_5885_, 0);
lean_inc(v_a_5886_);
lean_dec_ref_known(v___x_5885_, 1);
v___x_5887_ = l_Lean_Meta_mkLambdaFVars(v___x_5849_, v_a_5886_, v___x_5850_, v___x_5851_, v___x_5850_, v___x_5851_, v___x_5852_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
lean_dec_ref(v___x_5849_);
if (lean_obj_tag(v___x_5887_) == 0)
{
lean_object* v_a_5888_; 
v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
lean_inc(v_a_5888_);
lean_dec_ref_known(v___x_5887_, 1);
v_declValue_5856_ = v_a_5888_;
v___y_5857_ = v___y_5840_;
v___y_5858_ = v___y_5841_;
v___y_5859_ = v___y_5842_;
v___y_5860_ = v___y_5843_;
goto v___jp_5855_;
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec(v_a_5854_);
lean_dec(v_levelParams_5836_);
lean_dec(v_a_5835_);
lean_dec(v_enumName_5834_);
v_a_5889_ = lean_ctor_get(v___x_5887_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5887_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5887_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5887_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec(v_a_5854_);
lean_dec_ref(v___x_5849_);
lean_dec(v_levelParams_5836_);
lean_dec(v_a_5835_);
lean_dec(v_enumName_5834_);
v_a_5897_ = lean_ctor_get(v___x_5885_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5885_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5885_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5885_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
else
{
lean_object* v___x_5905_; 
lean_dec_ref(v_y_5839_);
lean_dec(v___x_5838_);
lean_dec_ref(v_x_5832_);
lean_inc_ref(v_P_5831_);
v___x_5905_ = l_Lean_mkArrow(v_P_5831_, v_P_5831_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5907_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
lean_inc(v_a_5906_);
lean_dec_ref_known(v___x_5905_, 1);
v___x_5907_ = l_Lean_Meta_mkLambdaFVars(v___x_5849_, v_a_5906_, v___x_5850_, v___x_5851_, v___x_5850_, v___x_5851_, v___x_5852_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
lean_dec_ref(v___x_5849_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v_a_5908_; 
v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
lean_inc(v_a_5908_);
lean_dec_ref_known(v___x_5907_, 1);
v_declValue_5856_ = v_a_5908_;
v___y_5857_ = v___y_5840_;
v___y_5858_ = v___y_5841_;
v___y_5859_ = v___y_5842_;
v___y_5860_ = v___y_5843_;
goto v___jp_5855_;
}
else
{
lean_object* v_a_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_5916_; 
lean_dec(v_a_5854_);
lean_dec(v_levelParams_5836_);
lean_dec(v_a_5835_);
lean_dec(v_enumName_5834_);
v_a_5909_ = lean_ctor_get(v___x_5907_, 0);
v_isSharedCheck_5916_ = !lean_is_exclusive(v___x_5907_);
if (v_isSharedCheck_5916_ == 0)
{
v___x_5911_ = v___x_5907_;
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_a_5909_);
lean_dec(v___x_5907_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
v_resetjp_5910_:
{
lean_object* v___x_5914_; 
if (v_isShared_5912_ == 0)
{
v___x_5914_ = v___x_5911_;
goto v_reusejp_5913_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_a_5909_);
v___x_5914_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
return v___x_5914_;
}
}
}
}
else
{
lean_object* v_a_5917_; lean_object* v___x_5919_; uint8_t v_isShared_5920_; uint8_t v_isSharedCheck_5924_; 
lean_dec(v_a_5854_);
lean_dec_ref(v___x_5849_);
lean_dec(v_levelParams_5836_);
lean_dec(v_a_5835_);
lean_dec(v_enumName_5834_);
v_a_5917_ = lean_ctor_get(v___x_5905_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5905_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5919_ = v___x_5905_;
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
else
{
lean_inc(v_a_5917_);
lean_dec(v___x_5905_);
v___x_5919_ = lean_box(0);
v_isShared_5920_ = v_isSharedCheck_5924_;
goto v_resetjp_5918_;
}
v_resetjp_5918_:
{
lean_object* v___x_5922_; 
if (v_isShared_5920_ == 0)
{
v___x_5922_ = v___x_5919_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5923_; 
v_reuseFailAlloc_5923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_a_5917_);
v___x_5922_ = v_reuseFailAlloc_5923_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
return v___x_5922_;
}
}
}
}
v___jp_5855_:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; uint8_t v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; 
v___x_5861_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_5862_ = l_Lean_Name_str___override(v_enumName_5834_, v___x_5861_);
v___x_5863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5863_, 0, v_a_5835_);
lean_ctor_set(v___x_5863_, 1, v_levelParams_5836_);
lean_inc_n(v___x_5862_, 2);
v___x_5864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5864_, 0, v___x_5862_);
lean_ctor_set(v___x_5864_, 1, v___x_5863_);
lean_ctor_set(v___x_5864_, 2, v_a_5854_);
v___x_5865_ = lean_box(1);
v___x_5866_ = 1;
v___x_5867_ = lean_box(0);
v___x_5868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5862_);
lean_ctor_set(v___x_5868_, 1, v___x_5867_);
v___x_5869_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5869_, 0, v___x_5864_);
lean_ctor_set(v___x_5869_, 1, v_declValue_5856_);
lean_ctor_set(v___x_5869_, 2, v___x_5865_);
lean_ctor_set(v___x_5869_, 3, v___x_5868_);
lean_ctor_set_uint8(v___x_5869_, sizeof(void*)*4, v___x_5866_);
v___x_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5870_, 0, v___x_5869_);
v___x_5871_ = l_Lean_addDecl(v___x_5870_, v___x_5850_, v___y_5859_, v___y_5860_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v___x_5872_; 
lean_dec_ref_known(v___x_5871_, 1);
v___x_5872_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_5862_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_);
return v___x_5872_;
}
else
{
lean_dec(v___x_5862_);
return v___x_5871_;
}
}
}
else
{
lean_object* v_a_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5932_; 
lean_dec_ref(v___x_5849_);
lean_dec_ref(v_y_5839_);
lean_dec(v___x_5838_);
lean_dec(v_levelParams_5836_);
lean_dec(v_a_5835_);
lean_dec(v_enumName_5834_);
lean_dec_ref(v_x_5832_);
lean_dec_ref(v_P_5831_);
v_a_5925_ = lean_ctor_get(v___x_5853_, 0);
v_isSharedCheck_5932_ = !lean_is_exclusive(v___x_5853_);
if (v_isSharedCheck_5932_ == 0)
{
v___x_5927_ = v___x_5853_;
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_a_5925_);
lean_dec(v___x_5853_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5930_; 
if (v_isShared_5928_ == 0)
{
v___x_5930_ = v___x_5927_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5925_);
v___x_5930_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
return v___x_5930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed(lean_object* v_P_5933_, lean_object* v_x_5934_, lean_object* v___x_5935_, lean_object* v_enumName_5936_, lean_object* v_a_5937_, lean_object* v_levelParams_5938_, lean_object* v_val_5939_, lean_object* v___x_5940_, lean_object* v_y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_){
_start:
{
lean_object* v_res_5947_; 
v_res_5947_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(v_P_5933_, v_x_5934_, v___x_5935_, v_enumName_5936_, v_a_5937_, v_levelParams_5938_, v_val_5939_, v___x_5940_, v_y_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_);
lean_dec(v___y_5945_);
lean_dec_ref(v___y_5944_);
lean_dec(v___y_5943_);
lean_dec_ref(v___y_5942_);
lean_dec_ref(v_val_5939_);
return v_res_5947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(lean_object* v_P_5951_, lean_object* v___x_5952_, lean_object* v_enumName_5953_, lean_object* v_a_5954_, lean_object* v_levelParams_5955_, lean_object* v_val_5956_, lean_object* v___x_5957_, lean_object* v___x_5958_, lean_object* v_x_5959_, lean_object* v___y_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_){
_start:
{
lean_object* v___f_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___f_5965_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed), 14, 8);
lean_closure_set(v___f_5965_, 0, v_P_5951_);
lean_closure_set(v___f_5965_, 1, v_x_5959_);
lean_closure_set(v___f_5965_, 2, v___x_5952_);
lean_closure_set(v___f_5965_, 3, v_enumName_5953_);
lean_closure_set(v___f_5965_, 4, v_a_5954_);
lean_closure_set(v___f_5965_, 5, v_levelParams_5955_);
lean_closure_set(v___f_5965_, 6, v_val_5956_);
lean_closure_set(v___f_5965_, 7, v___x_5957_);
v___x_5966_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_5967_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5966_, v___x_5958_, v___f_5965_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_);
return v___x_5967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed(lean_object* v_P_5968_, lean_object* v___x_5969_, lean_object* v_enumName_5970_, lean_object* v_a_5971_, lean_object* v_levelParams_5972_, lean_object* v_val_5973_, lean_object* v___x_5974_, lean_object* v___x_5975_, lean_object* v_x_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_){
_start:
{
lean_object* v_res_5982_; 
v_res_5982_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(v_P_5968_, v___x_5969_, v_enumName_5970_, v_a_5971_, v_levelParams_5972_, v_val_5973_, v___x_5974_, v___x_5975_, v_x_5976_, v___y_5977_, v___y_5978_, v___y_5979_, v___y_5980_);
lean_dec(v___y_5980_);
lean_dec_ref(v___y_5979_);
lean_dec(v___y_5978_);
lean_dec_ref(v___y_5977_);
return v_res_5982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(lean_object* v___x_5986_, lean_object* v_enumName_5987_, lean_object* v_a_5988_, lean_object* v_levelParams_5989_, lean_object* v_val_5990_, lean_object* v___x_5991_, lean_object* v___x_5992_, lean_object* v_P_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
lean_object* v___f_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
lean_inc_ref(v___x_5992_);
v___f_5999_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed), 14, 8);
lean_closure_set(v___f_5999_, 0, v_P_5993_);
lean_closure_set(v___f_5999_, 1, v___x_5986_);
lean_closure_set(v___f_5999_, 2, v_enumName_5987_);
lean_closure_set(v___f_5999_, 3, v_a_5988_);
lean_closure_set(v___f_5999_, 4, v_levelParams_5989_);
lean_closure_set(v___f_5999_, 5, v_val_5990_);
lean_closure_set(v___f_5999_, 6, v___x_5991_);
lean_closure_set(v___f_5999_, 7, v___x_5992_);
v___x_6000_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_6001_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6000_, v___x_5992_, v___f_5999_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_);
return v___x_6001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed(lean_object* v___x_6002_, lean_object* v_enumName_6003_, lean_object* v_a_6004_, lean_object* v_levelParams_6005_, lean_object* v_val_6006_, lean_object* v___x_6007_, lean_object* v___x_6008_, lean_object* v_P_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_){
_start:
{
lean_object* v_res_6015_; 
v_res_6015_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(v___x_6002_, v_enumName_6003_, v_a_6004_, v_levelParams_6005_, v_val_6006_, v___x_6007_, v___x_6008_, v_P_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec(v___y_6011_);
lean_dec_ref(v___y_6010_);
return v_res_6015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3(void){
_start:
{
lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6020_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_6021_ = lean_unsigned_to_nat(63u);
v___x_6022_ = lean_unsigned_to_nat(375u);
v___x_6023_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2));
v___x_6024_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_6025_ = l_mkPanicMessageWithDecl(v___x_6024_, v___x_6023_, v___x_6022_, v___x_6021_, v___x_6020_);
return v___x_6025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(lean_object* v_enumName_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_){
_start:
{
lean_object* v___x_6032_; 
lean_inc(v_enumName_6026_);
v___x_6032_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
if (lean_obj_tag(v___x_6032_) == 0)
{
lean_object* v_a_6033_; 
v_a_6033_ = lean_ctor_get(v___x_6032_, 0);
lean_inc(v_a_6033_);
lean_dec_ref_known(v___x_6032_, 1);
if (lean_obj_tag(v_a_6033_) == 5)
{
lean_object* v_val_6034_; lean_object* v_toConstantVal_6035_; lean_object* v_levelParams_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; 
v_val_6034_ = lean_ctor_get(v_a_6033_, 0);
lean_inc_ref(v_val_6034_);
lean_dec_ref_known(v_a_6033_, 1);
v_toConstantVal_6035_ = lean_ctor_get(v_val_6034_, 0);
v_levelParams_6036_ = lean_ctor_get(v_toConstantVal_6035_, 1);
lean_inc_n(v_levelParams_6036_, 2);
v___x_6037_ = lean_box(0);
v___x_6038_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_6036_, v___x_6037_);
v___x_6039_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_6040_ = l_Lean_Core_mkFreshUserName(v___x_6039_, v_a_6029_, v_a_6030_);
if (lean_obj_tag(v___x_6040_) == 0)
{
lean_object* v_a_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___f_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; 
v_a_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc_n(v_a_6041_, 2);
lean_dec_ref_known(v___x_6040_, 1);
lean_inc(v___x_6038_);
lean_inc(v_enumName_6026_);
v___x_6042_ = l_Lean_mkConst(v_enumName_6026_, v___x_6038_);
v___x_6043_ = l_Lean_mkLevelParam(v_a_6041_);
v___x_6044_ = l_Lean_mkSort(v___x_6043_);
lean_inc_ref(v___x_6044_);
v___f_6045_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed), 13, 7);
lean_closure_set(v___f_6045_, 0, v___x_6044_);
lean_closure_set(v___f_6045_, 1, v_enumName_6026_);
lean_closure_set(v___f_6045_, 2, v_a_6041_);
lean_closure_set(v___f_6045_, 3, v_levelParams_6036_);
lean_closure_set(v___f_6045_, 4, v_val_6034_);
lean_closure_set(v___f_6045_, 5, v___x_6038_);
lean_closure_set(v___f_6045_, 6, v___x_6042_);
v___x_6046_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_6047_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6046_, v___x_6044_, v___f_6045_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
return v___x_6047_;
}
else
{
lean_object* v_a_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6055_; 
lean_dec(v___x_6038_);
lean_dec(v_levelParams_6036_);
lean_dec_ref(v_val_6034_);
lean_dec(v_enumName_6026_);
v_a_6048_ = lean_ctor_get(v___x_6040_, 0);
v_isSharedCheck_6055_ = !lean_is_exclusive(v___x_6040_);
if (v_isSharedCheck_6055_ == 0)
{
v___x_6050_ = v___x_6040_;
v_isShared_6051_ = v_isSharedCheck_6055_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_a_6048_);
lean_dec(v___x_6040_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6055_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v___x_6053_; 
if (v_isShared_6051_ == 0)
{
v___x_6053_ = v___x_6050_;
goto v_reusejp_6052_;
}
else
{
lean_object* v_reuseFailAlloc_6054_; 
v_reuseFailAlloc_6054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6054_, 0, v_a_6048_);
v___x_6053_ = v_reuseFailAlloc_6054_;
goto v_reusejp_6052_;
}
v_reusejp_6052_:
{
return v___x_6053_;
}
}
}
}
else
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
lean_dec(v_a_6033_);
lean_dec(v_enumName_6026_);
v___x_6056_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3);
v___x_6057_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_6056_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
return v___x_6057_;
}
}
else
{
lean_object* v_a_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6065_; 
lean_dec(v_enumName_6026_);
v_a_6058_ = lean_ctor_get(v___x_6032_, 0);
v_isSharedCheck_6065_ = !lean_is_exclusive(v___x_6032_);
if (v_isSharedCheck_6065_ == 0)
{
v___x_6060_ = v___x_6032_;
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_a_6058_);
lean_dec(v___x_6032_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6063_; 
if (v_isShared_6061_ == 0)
{
v___x_6063_ = v___x_6060_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
v___x_6063_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
return v___x_6063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___boxed(lean_object* v_enumName_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_){
_start:
{
lean_object* v_res_6072_; 
v_res_6072_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6066_, v_a_6067_, v_a_6068_, v_a_6069_, v_a_6070_);
lean_dec(v_a_6070_);
lean_dec_ref(v_a_6069_);
lean_dec(v_a_6068_);
lean_dec_ref(v_a_6067_);
return v_res_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(uint8_t v___x_6073_, uint8_t v___x_6074_, uint8_t v___x_6075_, lean_object* v_p_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6082_ = lean_unsigned_to_nat(1u);
v___x_6083_ = lean_mk_empty_array_with_capacity(v___x_6082_);
lean_inc_ref(v_p_6076_);
v___x_6084_ = lean_array_push(v___x_6083_, v_p_6076_);
v___x_6085_ = l_Lean_Meta_mkLambdaFVars(v___x_6084_, v_p_6076_, v___x_6073_, v___x_6074_, v___x_6073_, v___x_6074_, v___x_6075_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
lean_dec_ref(v___x_6084_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed(lean_object* v___x_6086_, lean_object* v___x_6087_, lean_object* v___x_6088_, lean_object* v_p_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_){
_start:
{
uint8_t v___x_4229__boxed_6095_; uint8_t v___x_4230__boxed_6096_; uint8_t v___x_4231__boxed_6097_; lean_object* v_res_6098_; 
v___x_4229__boxed_6095_ = lean_unbox(v___x_6086_);
v___x_4230__boxed_6096_ = lean_unbox(v___x_6087_);
v___x_4231__boxed_6097_ = lean_unbox(v___x_6088_);
v_res_6098_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(v___x_4229__boxed_6095_, v___x_4230__boxed_6096_, v___x_4231__boxed_6097_, v_p_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
return v_res_6098_;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; 
v___x_6106_ = lean_box(0);
v___x_6107_ = lean_unsigned_to_nat(6u);
v___x_6108_ = lean_mk_empty_array_with_capacity(v___x_6107_);
v___x_6109_ = lean_array_push(v___x_6108_, v___x_6106_);
return v___x_6109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(lean_object* v_P_6113_, lean_object* v_x_6114_, lean_object* v_b_6115_, lean_object* v___x_6116_, uint8_t v___x_6117_, lean_object* v_enumName_6118_, lean_object* v_a_6119_, lean_object* v___x_6120_, lean_object* v_val_6121_, lean_object* v___x_6122_, lean_object* v_h_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; uint8_t v___x_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___f_6141_; lean_object* v___x_6142_; 
v___x_6129_ = lean_unsigned_to_nat(4u);
v___x_6130_ = lean_mk_empty_array_with_capacity(v___x_6129_);
lean_inc_ref_n(v_P_6113_, 2);
v___x_6131_ = lean_array_push(v___x_6130_, v_P_6113_);
lean_inc_ref_n(v_x_6114_, 2);
v___x_6132_ = lean_array_push(v___x_6131_, v_x_6114_);
lean_inc_ref_n(v_b_6115_, 2);
v___x_6133_ = lean_array_push(v___x_6132_, v_b_6115_);
lean_inc_ref(v_h_6123_);
v___x_6134_ = lean_array_push(v___x_6133_, v_h_6123_);
v___x_6135_ = l_Lean_mkApp3(v___x_6116_, v_P_6113_, v_x_6114_, v_b_6115_);
v___x_6136_ = 0;
v___x_6137_ = 1;
v___x_6138_ = lean_box(v___x_6136_);
v___x_6139_ = lean_box(v___x_6137_);
v___x_6140_ = lean_box(v___x_6117_);
v___f_6141_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed), 9, 3);
lean_closure_set(v___f_6141_, 0, v___x_6138_);
lean_closure_set(v___f_6141_, 1, v___x_6139_);
lean_closure_set(v___f_6141_, 2, v___x_6140_);
v___x_6142_ = l_Lean_Meta_mkForallFVars(v___x_6134_, v___x_6135_, v___x_6136_, v___x_6137_, v___x_6137_, v___x_6117_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
if (lean_obj_tag(v___x_6142_) == 0)
{
lean_object* v_a_6143_; lean_object* v_____do__lift_6145_; lean_object* v___y_6146_; lean_object* v___y_6147_; lean_object* v___y_6148_; lean_object* v___y_6149_; lean_object* v___x_6217_; lean_object* v___x_6218_; uint8_t v___x_6219_; 
v_a_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc(v_a_6143_);
lean_dec_ref_known(v___x_6142_, 1);
v___x_6217_ = l_Lean_InductiveVal_numCtors(v_val_6121_);
v___x_6218_ = lean_unsigned_to_nat(1u);
v___x_6219_ = lean_nat_dec_eq(v___x_6217_, v___x_6218_);
lean_dec(v___x_6217_);
if (v___x_6219_ == 0)
{
lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
lean_dec_ref(v___f_6141_);
v___x_6220_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6122_);
v___x_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6222_, 0, v_P_6113_);
v___x_6223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6223_, 0, v_x_6114_);
v___x_6224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6224_, 0, v_b_6115_);
v___x_6225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6225_, 0, v_h_6123_);
v___x_6226_ = lean_obj_once(&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3, &l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3_once, _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3);
v___x_6227_ = lean_array_push(v___x_6226_, v___x_6221_);
v___x_6228_ = lean_array_push(v___x_6227_, v___x_6222_);
v___x_6229_ = lean_array_push(v___x_6228_, v___x_6223_);
v___x_6230_ = lean_array_push(v___x_6229_, v___x_6224_);
v___x_6231_ = lean_array_push(v___x_6230_, v___x_6225_);
v___x_6232_ = l_Lean_Meta_mkAppOptM(v___x_6220_, v___x_6231_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
if (lean_obj_tag(v___x_6232_) == 0)
{
lean_object* v_a_6233_; 
v_a_6233_ = lean_ctor_get(v___x_6232_, 0);
lean_inc(v_a_6233_);
lean_dec_ref_known(v___x_6232_, 1);
v_____do__lift_6145_ = v_a_6233_;
v___y_6146_ = v___y_6124_;
v___y_6147_ = v___y_6125_;
v___y_6148_ = v___y_6126_;
v___y_6149_ = v___y_6127_;
goto v___jp_6144_;
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec(v_a_6143_);
lean_dec_ref(v___x_6134_);
lean_dec(v___x_6120_);
lean_dec(v_a_6119_);
lean_dec(v_enumName_6118_);
v_a_6234_ = lean_ctor_get(v___x_6232_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6232_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6232_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6232_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
else
{
lean_object* v___x_6242_; lean_object* v___x_6243_; 
lean_dec_ref(v_h_6123_);
lean_dec_ref(v___x_6122_);
lean_dec_ref(v_b_6115_);
lean_dec_ref(v_x_6114_);
v___x_6242_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5));
v___x_6243_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6242_, v_P_6113_, v___f_6141_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
if (lean_obj_tag(v___x_6243_) == 0)
{
lean_object* v_a_6244_; 
v_a_6244_ = lean_ctor_get(v___x_6243_, 0);
lean_inc(v_a_6244_);
lean_dec_ref_known(v___x_6243_, 1);
v_____do__lift_6145_ = v_a_6244_;
v___y_6146_ = v___y_6124_;
v___y_6147_ = v___y_6125_;
v___y_6148_ = v___y_6126_;
v___y_6149_ = v___y_6127_;
goto v___jp_6144_;
}
else
{
lean_object* v_a_6245_; lean_object* v___x_6247_; uint8_t v_isShared_6248_; uint8_t v_isSharedCheck_6252_; 
lean_dec(v_a_6143_);
lean_dec_ref(v___x_6134_);
lean_dec(v___x_6120_);
lean_dec(v_a_6119_);
lean_dec(v_enumName_6118_);
v_a_6245_ = lean_ctor_get(v___x_6243_, 0);
v_isSharedCheck_6252_ = !lean_is_exclusive(v___x_6243_);
if (v_isSharedCheck_6252_ == 0)
{
v___x_6247_ = v___x_6243_;
v_isShared_6248_ = v_isSharedCheck_6252_;
goto v_resetjp_6246_;
}
else
{
lean_inc(v_a_6245_);
lean_dec(v___x_6243_);
v___x_6247_ = lean_box(0);
v_isShared_6248_ = v_isSharedCheck_6252_;
goto v_resetjp_6246_;
}
v_resetjp_6246_:
{
lean_object* v___x_6250_; 
if (v_isShared_6248_ == 0)
{
v___x_6250_ = v___x_6247_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6251_; 
v_reuseFailAlloc_6251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6245_);
v___x_6250_ = v_reuseFailAlloc_6251_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
return v___x_6250_;
}
}
}
}
v___jp_6144_:
{
lean_object* v___x_6150_; 
v___x_6150_ = l_Lean_Meta_mkLambdaFVars(v___x_6134_, v_____do__lift_6145_, v___x_6136_, v___x_6137_, v___x_6136_, v___x_6137_, v___x_6117_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
lean_dec_ref(v___x_6134_);
if (lean_obj_tag(v___x_6150_) == 0)
{
lean_object* v_a_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; uint8_t v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; 
v_a_6151_ = lean_ctor_get(v___x_6150_, 0);
lean_inc(v_a_6151_);
lean_dec_ref_known(v___x_6150_, 1);
v___x_6152_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_6153_ = l_Lean_Name_str___override(v_enumName_6118_, v___x_6152_);
v___x_6154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6154_, 0, v_a_6119_);
lean_ctor_set(v___x_6154_, 1, v___x_6120_);
lean_inc_n(v___x_6153_, 2);
v___x_6155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6155_, 0, v___x_6153_);
lean_ctor_set(v___x_6155_, 1, v___x_6154_);
lean_ctor_set(v___x_6155_, 2, v_a_6143_);
v___x_6156_ = lean_box(1);
v___x_6157_ = 1;
v___x_6158_ = lean_box(0);
v___x_6159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6153_);
lean_ctor_set(v___x_6159_, 1, v___x_6158_);
v___x_6160_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6160_, 0, v___x_6155_);
lean_ctor_set(v___x_6160_, 1, v_a_6151_);
lean_ctor_set(v___x_6160_, 2, v___x_6156_);
lean_ctor_set(v___x_6160_, 3, v___x_6159_);
lean_ctor_set_uint8(v___x_6160_, sizeof(void*)*4, v___x_6157_);
v___x_6161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6161_, 0, v___x_6160_);
v___x_6162_ = l_Lean_addDecl(v___x_6161_, v___x_6136_, v___y_6148_, v___y_6149_);
if (lean_obj_tag(v___x_6162_) == 0)
{
lean_object* v___x_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6207_; 
lean_dec_ref_known(v___x_6162_, 1);
lean_inc(v___x_6153_);
v___x_6163_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_6153_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
v_isSharedCheck_6207_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6207_ == 0)
{
lean_object* v_unused_6208_; 
v_unused_6208_ = lean_ctor_get(v___x_6163_, 0);
lean_dec(v_unused_6208_);
v___x_6165_ = v___x_6163_;
v_isShared_6166_ = v_isSharedCheck_6207_;
goto v_resetjp_6164_;
}
else
{
lean_dec(v___x_6163_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6207_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6167_; lean_object* v_env_6168_; lean_object* v_nextMacroScope_6169_; lean_object* v_ngen_6170_; lean_object* v_auxDeclNGen_6171_; lean_object* v_traceState_6172_; lean_object* v_messages_6173_; lean_object* v_infoState_6174_; lean_object* v_snapshotTasks_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6205_; 
v___x_6167_ = lean_st_ref_take(v___y_6149_);
v_env_6168_ = lean_ctor_get(v___x_6167_, 0);
v_nextMacroScope_6169_ = lean_ctor_get(v___x_6167_, 1);
v_ngen_6170_ = lean_ctor_get(v___x_6167_, 2);
v_auxDeclNGen_6171_ = lean_ctor_get(v___x_6167_, 3);
v_traceState_6172_ = lean_ctor_get(v___x_6167_, 4);
v_messages_6173_ = lean_ctor_get(v___x_6167_, 6);
v_infoState_6174_ = lean_ctor_get(v___x_6167_, 7);
v_snapshotTasks_6175_ = lean_ctor_get(v___x_6167_, 8);
v_isSharedCheck_6205_ = !lean_is_exclusive(v___x_6167_);
if (v_isSharedCheck_6205_ == 0)
{
lean_object* v_unused_6206_; 
v_unused_6206_ = lean_ctor_get(v___x_6167_, 5);
lean_dec(v_unused_6206_);
v___x_6177_ = v___x_6167_;
v_isShared_6178_ = v_isSharedCheck_6205_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_snapshotTasks_6175_);
lean_inc(v_infoState_6174_);
lean_inc(v_messages_6173_);
lean_inc(v_traceState_6172_);
lean_inc(v_auxDeclNGen_6171_);
lean_inc(v_ngen_6170_);
lean_inc(v_nextMacroScope_6169_);
lean_inc(v_env_6168_);
lean_dec(v___x_6167_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6205_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6183_; 
v___x_6179_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0));
v___x_6180_ = l_Lean_markNoConfusion(v_env_6168_, v___x_6153_, v___x_6179_);
v___x_6181_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_6178_ == 0)
{
lean_ctor_set(v___x_6177_, 5, v___x_6181_);
lean_ctor_set(v___x_6177_, 0, v___x_6180_);
v___x_6183_ = v___x_6177_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v___x_6180_);
lean_ctor_set(v_reuseFailAlloc_6204_, 1, v_nextMacroScope_6169_);
lean_ctor_set(v_reuseFailAlloc_6204_, 2, v_ngen_6170_);
lean_ctor_set(v_reuseFailAlloc_6204_, 3, v_auxDeclNGen_6171_);
lean_ctor_set(v_reuseFailAlloc_6204_, 4, v_traceState_6172_);
lean_ctor_set(v_reuseFailAlloc_6204_, 5, v___x_6181_);
lean_ctor_set(v_reuseFailAlloc_6204_, 6, v_messages_6173_);
lean_ctor_set(v_reuseFailAlloc_6204_, 7, v_infoState_6174_);
lean_ctor_set(v_reuseFailAlloc_6204_, 8, v_snapshotTasks_6175_);
v___x_6183_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v_mctx_6186_; lean_object* v_zetaDeltaFVarIds_6187_; lean_object* v_postponed_6188_; lean_object* v_diag_6189_; lean_object* v___x_6191_; uint8_t v_isShared_6192_; uint8_t v_isSharedCheck_6202_; 
v___x_6184_ = lean_st_ref_put(v___y_6149_, v___x_6183_);
v___x_6185_ = lean_st_ref_take(v___y_6147_);
v_mctx_6186_ = lean_ctor_get(v___x_6185_, 0);
v_zetaDeltaFVarIds_6187_ = lean_ctor_get(v___x_6185_, 2);
v_postponed_6188_ = lean_ctor_get(v___x_6185_, 3);
v_diag_6189_ = lean_ctor_get(v___x_6185_, 4);
v_isSharedCheck_6202_ = !lean_is_exclusive(v___x_6185_);
if (v_isSharedCheck_6202_ == 0)
{
lean_object* v_unused_6203_; 
v_unused_6203_ = lean_ctor_get(v___x_6185_, 1);
lean_dec(v_unused_6203_);
v___x_6191_ = v___x_6185_;
v_isShared_6192_ = v_isSharedCheck_6202_;
goto v_resetjp_6190_;
}
else
{
lean_inc(v_diag_6189_);
lean_inc(v_postponed_6188_);
lean_inc(v_zetaDeltaFVarIds_6187_);
lean_inc(v_mctx_6186_);
lean_dec(v___x_6185_);
v___x_6191_ = lean_box(0);
v_isShared_6192_ = v_isSharedCheck_6202_;
goto v_resetjp_6190_;
}
v_resetjp_6190_:
{
lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6196_; 
v___x_6193_ = lean_box(0);
v___x_6194_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_6192_ == 0)
{
lean_ctor_set(v___x_6191_, 1, v___x_6194_);
v___x_6196_ = v___x_6191_;
goto v_reusejp_6195_;
}
else
{
lean_object* v_reuseFailAlloc_6201_; 
v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_mctx_6186_);
lean_ctor_set(v_reuseFailAlloc_6201_, 1, v___x_6194_);
lean_ctor_set(v_reuseFailAlloc_6201_, 2, v_zetaDeltaFVarIds_6187_);
lean_ctor_set(v_reuseFailAlloc_6201_, 3, v_postponed_6188_);
lean_ctor_set(v_reuseFailAlloc_6201_, 4, v_diag_6189_);
v___x_6196_ = v_reuseFailAlloc_6201_;
goto v_reusejp_6195_;
}
v_reusejp_6195_:
{
lean_object* v___x_6197_; lean_object* v___x_6199_; 
v___x_6197_ = lean_st_ref_put(v___y_6147_, v___x_6196_);
if (v_isShared_6166_ == 0)
{
lean_ctor_set(v___x_6165_, 0, v___x_6193_);
v___x_6199_ = v___x_6165_;
goto v_reusejp_6198_;
}
else
{
lean_object* v_reuseFailAlloc_6200_; 
v_reuseFailAlloc_6200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6200_, 0, v___x_6193_);
v___x_6199_ = v_reuseFailAlloc_6200_;
goto v_reusejp_6198_;
}
v_reusejp_6198_:
{
return v___x_6199_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_6153_);
return v___x_6162_;
}
}
else
{
lean_object* v_a_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6216_; 
lean_dec(v_a_6143_);
lean_dec(v___x_6120_);
lean_dec(v_a_6119_);
lean_dec(v_enumName_6118_);
v_a_6209_ = lean_ctor_get(v___x_6150_, 0);
v_isSharedCheck_6216_ = !lean_is_exclusive(v___x_6150_);
if (v_isSharedCheck_6216_ == 0)
{
v___x_6211_ = v___x_6150_;
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_a_6209_);
lean_dec(v___x_6150_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6214_; 
if (v_isShared_6212_ == 0)
{
v___x_6214_ = v___x_6211_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6215_; 
v_reuseFailAlloc_6215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6215_, 0, v_a_6209_);
v___x_6214_ = v_reuseFailAlloc_6215_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
return v___x_6214_;
}
}
}
}
}
else
{
lean_object* v_a_6253_; lean_object* v___x_6255_; uint8_t v_isShared_6256_; uint8_t v_isSharedCheck_6260_; 
lean_dec_ref(v___f_6141_);
lean_dec_ref(v___x_6134_);
lean_dec_ref(v_h_6123_);
lean_dec_ref(v___x_6122_);
lean_dec(v___x_6120_);
lean_dec(v_a_6119_);
lean_dec(v_enumName_6118_);
lean_dec_ref(v_b_6115_);
lean_dec_ref(v_x_6114_);
lean_dec_ref(v_P_6113_);
v_a_6253_ = lean_ctor_get(v___x_6142_, 0);
v_isSharedCheck_6260_ = !lean_is_exclusive(v___x_6142_);
if (v_isSharedCheck_6260_ == 0)
{
v___x_6255_ = v___x_6142_;
v_isShared_6256_ = v_isSharedCheck_6260_;
goto v_resetjp_6254_;
}
else
{
lean_inc(v_a_6253_);
lean_dec(v___x_6142_);
v___x_6255_ = lean_box(0);
v_isShared_6256_ = v_isSharedCheck_6260_;
goto v_resetjp_6254_;
}
v_resetjp_6254_:
{
lean_object* v___x_6258_; 
if (v_isShared_6256_ == 0)
{
v___x_6258_ = v___x_6255_;
goto v_reusejp_6257_;
}
else
{
lean_object* v_reuseFailAlloc_6259_; 
v_reuseFailAlloc_6259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6259_, 0, v_a_6253_);
v___x_6258_ = v_reuseFailAlloc_6259_;
goto v_reusejp_6257_;
}
v_reusejp_6257_:
{
return v___x_6258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed(lean_object* v_P_6261_, lean_object* v_x_6262_, lean_object* v_b_6263_, lean_object* v___x_6264_, lean_object* v___x_6265_, lean_object* v_enumName_6266_, lean_object* v_a_6267_, lean_object* v___x_6268_, lean_object* v_val_6269_, lean_object* v___x_6270_, lean_object* v_h_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
uint8_t v___x_4304__boxed_6277_; lean_object* v_res_6278_; 
v___x_4304__boxed_6277_ = lean_unbox(v___x_6265_);
v_res_6278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(v_P_6261_, v_x_6262_, v_b_6263_, v___x_6264_, v___x_4304__boxed_6277_, v_enumName_6266_, v_a_6267_, v___x_6268_, v_val_6269_, v___x_6270_, v_h_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
lean_dec_ref(v_val_6269_);
return v_res_6278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(lean_object* v_P_6279_, lean_object* v_x_6280_, lean_object* v___x_6281_, uint8_t v___x_6282_, lean_object* v_enumName_6283_, lean_object* v_a_6284_, lean_object* v___x_6285_, lean_object* v_val_6286_, lean_object* v___x_6287_, lean_object* v_b_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_){
_start:
{
lean_object* v___x_6294_; lean_object* v___f_6295_; lean_object* v___x_6296_; 
v___x_6294_ = lean_box(v___x_6282_);
lean_inc_ref(v_b_6288_);
lean_inc_ref(v_x_6280_);
v___f_6295_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed), 16, 10);
lean_closure_set(v___f_6295_, 0, v_P_6279_);
lean_closure_set(v___f_6295_, 1, v_x_6280_);
lean_closure_set(v___f_6295_, 2, v_b_6288_);
lean_closure_set(v___f_6295_, 3, v___x_6281_);
lean_closure_set(v___f_6295_, 4, v___x_6294_);
lean_closure_set(v___f_6295_, 5, v_enumName_6283_);
lean_closure_set(v___f_6295_, 6, v_a_6284_);
lean_closure_set(v___f_6295_, 7, v___x_6285_);
lean_closure_set(v___f_6295_, 8, v_val_6286_);
lean_closure_set(v___f_6295_, 9, v___x_6287_);
v___x_6296_ = l_Lean_Meta_mkEq(v_x_6280_, v_b_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
if (lean_obj_tag(v___x_6296_) == 0)
{
lean_object* v_a_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v_a_6297_ = lean_ctor_get(v___x_6296_, 0);
lean_inc(v_a_6297_);
lean_dec_ref_known(v___x_6296_, 1);
v___x_6298_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13));
v___x_6299_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6298_, v_a_6297_, v___f_6295_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_);
return v___x_6299_;
}
else
{
lean_object* v_a_6300_; lean_object* v___x_6302_; uint8_t v_isShared_6303_; uint8_t v_isSharedCheck_6307_; 
lean_dec_ref(v___f_6295_);
v_a_6300_ = lean_ctor_get(v___x_6296_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6296_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6302_ = v___x_6296_;
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
else
{
lean_inc(v_a_6300_);
lean_dec(v___x_6296_);
v___x_6302_ = lean_box(0);
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
v_resetjp_6301_:
{
lean_object* v___x_6305_; 
if (v_isShared_6303_ == 0)
{
v___x_6305_ = v___x_6302_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed(lean_object* v_P_6308_, lean_object* v_x_6309_, lean_object* v___x_6310_, lean_object* v___x_6311_, lean_object* v_enumName_6312_, lean_object* v_a_6313_, lean_object* v___x_6314_, lean_object* v_val_6315_, lean_object* v___x_6316_, lean_object* v_b_6317_, lean_object* v___y_6318_, lean_object* v___y_6319_, lean_object* v___y_6320_, lean_object* v___y_6321_, lean_object* v___y_6322_){
_start:
{
uint8_t v___x_4598__boxed_6323_; lean_object* v_res_6324_; 
v___x_4598__boxed_6323_ = lean_unbox(v___x_6311_);
v_res_6324_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(v_P_6308_, v_x_6309_, v___x_6310_, v___x_4598__boxed_6323_, v_enumName_6312_, v_a_6313_, v___x_6314_, v_val_6315_, v___x_6316_, v_b_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
lean_dec(v___y_6321_);
lean_dec_ref(v___y_6320_);
lean_dec(v___y_6319_);
lean_dec_ref(v___y_6318_);
return v_res_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(lean_object* v_P_6325_, lean_object* v_x_6326_, lean_object* v___x_6327_, lean_object* v_enumName_6328_, lean_object* v_a_6329_, lean_object* v___x_6330_, lean_object* v_val_6331_, lean_object* v___x_6332_, lean_object* v_name_6333_, uint8_t v_bi_6334_, lean_object* v_type_6335_, uint8_t v_kind_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
uint8_t v___x_6342_; lean_object* v___x_6343_; lean_object* v___f_6344_; lean_object* v___x_6345_; 
v___x_6342_ = 1;
v___x_6343_ = lean_box(v___x_6342_);
v___f_6344_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed), 15, 9);
lean_closure_set(v___f_6344_, 0, v_P_6325_);
lean_closure_set(v___f_6344_, 1, v_x_6326_);
lean_closure_set(v___f_6344_, 2, v___x_6327_);
lean_closure_set(v___f_6344_, 3, v___x_6343_);
lean_closure_set(v___f_6344_, 4, v_enumName_6328_);
lean_closure_set(v___f_6344_, 5, v_a_6329_);
lean_closure_set(v___f_6344_, 6, v___x_6330_);
lean_closure_set(v___f_6344_, 7, v_val_6331_);
lean_closure_set(v___f_6344_, 8, v___x_6332_);
v___x_6345_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6333_, v_bi_6334_, v_type_6335_, v___f_6344_, v_kind_6336_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v_a_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6353_; 
v_a_6346_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6353_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6353_ == 0)
{
v___x_6348_ = v___x_6345_;
v_isShared_6349_ = v_isSharedCheck_6353_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_a_6346_);
lean_dec(v___x_6345_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6353_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v___x_6351_; 
if (v_isShared_6349_ == 0)
{
v___x_6351_ = v___x_6348_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_a_6346_);
v___x_6351_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
return v___x_6351_;
}
}
}
else
{
lean_object* v_a_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6361_; 
v_a_6354_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6361_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6361_ == 0)
{
v___x_6356_ = v___x_6345_;
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_a_6354_);
lean_dec(v___x_6345_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v___x_6359_; 
if (v_isShared_6357_ == 0)
{
v___x_6359_ = v___x_6356_;
goto v_reusejp_6358_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_a_6354_);
v___x_6359_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6358_;
}
v_reusejp_6358_:
{
return v___x_6359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___boxed(lean_object** _args){
lean_object* v_P_6362_ = _args[0];
lean_object* v_x_6363_ = _args[1];
lean_object* v___x_6364_ = _args[2];
lean_object* v_enumName_6365_ = _args[3];
lean_object* v_a_6366_ = _args[4];
lean_object* v___x_6367_ = _args[5];
lean_object* v_val_6368_ = _args[6];
lean_object* v___x_6369_ = _args[7];
lean_object* v_name_6370_ = _args[8];
lean_object* v_bi_6371_ = _args[9];
lean_object* v_type_6372_ = _args[10];
lean_object* v_kind_6373_ = _args[11];
lean_object* v___y_6374_ = _args[12];
lean_object* v___y_6375_ = _args[13];
lean_object* v___y_6376_ = _args[14];
lean_object* v___y_6377_ = _args[15];
lean_object* v___y_6378_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6379_; uint8_t v_kind_boxed_6380_; lean_object* v_res_6381_; 
v_bi_boxed_6379_ = lean_unbox(v_bi_6371_);
v_kind_boxed_6380_ = lean_unbox(v_kind_6373_);
v_res_6381_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6362_, v_x_6363_, v___x_6364_, v_enumName_6365_, v_a_6366_, v___x_6367_, v_val_6368_, v___x_6369_, v_name_6370_, v_bi_boxed_6379_, v_type_6372_, v_kind_boxed_6380_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_);
lean_dec(v___y_6377_);
lean_dec_ref(v___y_6376_);
lean_dec(v___y_6375_);
lean_dec_ref(v___y_6374_);
return v_res_6381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(lean_object* v_P_6382_, lean_object* v___x_6383_, lean_object* v_enumName_6384_, lean_object* v_a_6385_, lean_object* v___x_6386_, lean_object* v_val_6387_, lean_object* v___x_6388_, uint8_t v___x_6389_, lean_object* v___x_6390_, lean_object* v_b_6391_, lean_object* v___y_6392_, lean_object* v___y_6393_, lean_object* v___y_6394_, lean_object* v___y_6395_){
_start:
{
lean_object* v___x_6397_; uint8_t v___x_6398_; lean_object* v___x_6399_; 
v___x_6397_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_6398_ = 0;
v___x_6399_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6382_, v_b_6391_, v___x_6383_, v_enumName_6384_, v_a_6385_, v___x_6386_, v_val_6387_, v___x_6388_, v___x_6397_, v___x_6389_, v___x_6390_, v___x_6398_, v___y_6392_, v___y_6393_, v___y_6394_, v___y_6395_);
return v___x_6399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed(lean_object* v_P_6400_, lean_object* v___x_6401_, lean_object* v_enumName_6402_, lean_object* v_a_6403_, lean_object* v___x_6404_, lean_object* v_val_6405_, lean_object* v___x_6406_, lean_object* v___x_6407_, lean_object* v___x_6408_, lean_object* v_b_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_){
_start:
{
uint8_t v___x_4737__boxed_6415_; lean_object* v_res_6416_; 
v___x_4737__boxed_6415_ = lean_unbox(v___x_6407_);
v_res_6416_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(v_P_6400_, v___x_6401_, v_enumName_6402_, v_a_6403_, v___x_6404_, v_val_6405_, v___x_6406_, v___x_4737__boxed_6415_, v___x_6408_, v_b_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_);
lean_dec(v___y_6413_);
lean_dec_ref(v___y_6412_);
lean_dec(v___y_6411_);
lean_dec_ref(v___y_6410_);
return v_res_6416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(lean_object* v_P_6417_, lean_object* v___x_6418_, lean_object* v_enumName_6419_, lean_object* v_a_6420_, lean_object* v___x_6421_, lean_object* v_val_6422_, lean_object* v___x_6423_, lean_object* v___x_6424_, lean_object* v_name_6425_, uint8_t v_bi_6426_, lean_object* v_type_6427_, uint8_t v_kind_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_, lean_object* v___y_6432_){
_start:
{
uint8_t v___x_6434_; lean_object* v___x_6435_; lean_object* v___f_6436_; lean_object* v___x_6437_; 
v___x_6434_ = 1;
v___x_6435_ = lean_box(v___x_6434_);
v___f_6436_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed), 15, 9);
lean_closure_set(v___f_6436_, 0, v_P_6417_);
lean_closure_set(v___f_6436_, 1, v___x_6418_);
lean_closure_set(v___f_6436_, 2, v_enumName_6419_);
lean_closure_set(v___f_6436_, 3, v_a_6420_);
lean_closure_set(v___f_6436_, 4, v___x_6421_);
lean_closure_set(v___f_6436_, 5, v_val_6422_);
lean_closure_set(v___f_6436_, 6, v___x_6423_);
lean_closure_set(v___f_6436_, 7, v___x_6435_);
lean_closure_set(v___f_6436_, 8, v___x_6424_);
v___x_6437_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6425_, v_bi_6426_, v_type_6427_, v___f_6436_, v_kind_6428_, v___y_6429_, v___y_6430_, v___y_6431_, v___y_6432_);
if (lean_obj_tag(v___x_6437_) == 0)
{
lean_object* v_a_6438_; lean_object* v___x_6440_; uint8_t v_isShared_6441_; uint8_t v_isSharedCheck_6445_; 
v_a_6438_ = lean_ctor_get(v___x_6437_, 0);
v_isSharedCheck_6445_ = !lean_is_exclusive(v___x_6437_);
if (v_isSharedCheck_6445_ == 0)
{
v___x_6440_ = v___x_6437_;
v_isShared_6441_ = v_isSharedCheck_6445_;
goto v_resetjp_6439_;
}
else
{
lean_inc(v_a_6438_);
lean_dec(v___x_6437_);
v___x_6440_ = lean_box(0);
v_isShared_6441_ = v_isSharedCheck_6445_;
goto v_resetjp_6439_;
}
v_resetjp_6439_:
{
lean_object* v___x_6443_; 
if (v_isShared_6441_ == 0)
{
v___x_6443_ = v___x_6440_;
goto v_reusejp_6442_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_a_6438_);
v___x_6443_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6442_;
}
v_reusejp_6442_:
{
return v___x_6443_;
}
}
}
else
{
lean_object* v_a_6446_; lean_object* v___x_6448_; uint8_t v_isShared_6449_; uint8_t v_isSharedCheck_6453_; 
v_a_6446_ = lean_ctor_get(v___x_6437_, 0);
v_isSharedCheck_6453_ = !lean_is_exclusive(v___x_6437_);
if (v_isSharedCheck_6453_ == 0)
{
v___x_6448_ = v___x_6437_;
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
else
{
lean_inc(v_a_6446_);
lean_dec(v___x_6437_);
v___x_6448_ = lean_box(0);
v_isShared_6449_ = v_isSharedCheck_6453_;
goto v_resetjp_6447_;
}
v_resetjp_6447_:
{
lean_object* v___x_6451_; 
if (v_isShared_6449_ == 0)
{
v___x_6451_ = v___x_6448_;
goto v_reusejp_6450_;
}
else
{
lean_object* v_reuseFailAlloc_6452_; 
v_reuseFailAlloc_6452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6452_, 0, v_a_6446_);
v___x_6451_ = v_reuseFailAlloc_6452_;
goto v_reusejp_6450_;
}
v_reusejp_6450_:
{
return v___x_6451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___boxed(lean_object** _args){
lean_object* v_P_6454_ = _args[0];
lean_object* v___x_6455_ = _args[1];
lean_object* v_enumName_6456_ = _args[2];
lean_object* v_a_6457_ = _args[3];
lean_object* v___x_6458_ = _args[4];
lean_object* v_val_6459_ = _args[5];
lean_object* v___x_6460_ = _args[6];
lean_object* v___x_6461_ = _args[7];
lean_object* v_name_6462_ = _args[8];
lean_object* v_bi_6463_ = _args[9];
lean_object* v_type_6464_ = _args[10];
lean_object* v_kind_6465_ = _args[11];
lean_object* v___y_6466_ = _args[12];
lean_object* v___y_6467_ = _args[13];
lean_object* v___y_6468_ = _args[14];
lean_object* v___y_6469_ = _args[15];
lean_object* v___y_6470_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6471_; uint8_t v_kind_boxed_6472_; lean_object* v_res_6473_; 
v_bi_boxed_6471_ = lean_unbox(v_bi_6463_);
v_kind_boxed_6472_ = lean_unbox(v_kind_6465_);
v_res_6473_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_P_6454_, v___x_6455_, v_enumName_6456_, v_a_6457_, v___x_6458_, v_val_6459_, v___x_6460_, v___x_6461_, v_name_6462_, v_bi_boxed_6471_, v_type_6464_, v_kind_boxed_6472_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
lean_dec(v___y_6469_);
lean_dec_ref(v___y_6468_);
lean_dec(v___y_6467_);
lean_dec_ref(v___y_6466_);
return v_res_6473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(lean_object* v___x_6474_, lean_object* v_enumName_6475_, lean_object* v_a_6476_, lean_object* v___x_6477_, lean_object* v_val_6478_, lean_object* v___x_6479_, lean_object* v___x_6480_, uint8_t v___x_6481_, lean_object* v_b_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_){
_start:
{
lean_object* v___x_6488_; uint8_t v___x_6489_; lean_object* v___x_6490_; 
v___x_6488_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_6489_ = 0;
lean_inc_ref(v___x_6480_);
v___x_6490_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_b_6482_, v___x_6474_, v_enumName_6475_, v_a_6476_, v___x_6477_, v_val_6478_, v___x_6479_, v___x_6480_, v___x_6488_, v___x_6481_, v___x_6480_, v___x_6489_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_);
return v___x_6490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed(lean_object* v___x_6491_, lean_object* v_enumName_6492_, lean_object* v_a_6493_, lean_object* v___x_6494_, lean_object* v_val_6495_, lean_object* v___x_6496_, lean_object* v___x_6497_, lean_object* v___x_6498_, lean_object* v_b_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_){
_start:
{
uint8_t v___x_4857__boxed_6505_; lean_object* v_res_6506_; 
v___x_4857__boxed_6505_ = lean_unbox(v___x_6498_);
v_res_6506_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(v___x_6491_, v_enumName_6492_, v_a_6493_, v___x_6494_, v_val_6495_, v___x_6496_, v___x_6497_, v___x_4857__boxed_6505_, v_b_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_);
lean_dec(v___y_6503_);
lean_dec_ref(v___y_6502_);
lean_dec(v___y_6501_);
lean_dec_ref(v___y_6500_);
return v_res_6506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(lean_object* v___x_6507_, lean_object* v_enumName_6508_, lean_object* v_a_6509_, lean_object* v___x_6510_, lean_object* v_val_6511_, lean_object* v___x_6512_, lean_object* v___x_6513_, lean_object* v_name_6514_, uint8_t v_bi_6515_, lean_object* v_type_6516_, uint8_t v_kind_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_){
_start:
{
uint8_t v___x_6523_; lean_object* v___x_6524_; lean_object* v___f_6525_; lean_object* v___x_6526_; 
v___x_6523_ = 1;
v___x_6524_ = lean_box(v___x_6523_);
v___f_6525_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(v___f_6525_, 0, v___x_6507_);
lean_closure_set(v___f_6525_, 1, v_enumName_6508_);
lean_closure_set(v___f_6525_, 2, v_a_6509_);
lean_closure_set(v___f_6525_, 3, v___x_6510_);
lean_closure_set(v___f_6525_, 4, v_val_6511_);
lean_closure_set(v___f_6525_, 5, v___x_6512_);
lean_closure_set(v___f_6525_, 6, v___x_6513_);
lean_closure_set(v___f_6525_, 7, v___x_6524_);
v___x_6526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6514_, v_bi_6515_, v_type_6516_, v___f_6525_, v_kind_6517_, v___y_6518_, v___y_6519_, v___y_6520_, v___y_6521_);
if (lean_obj_tag(v___x_6526_) == 0)
{
lean_object* v_a_6527_; lean_object* v___x_6529_; uint8_t v_isShared_6530_; uint8_t v_isSharedCheck_6534_; 
v_a_6527_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6534_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6534_ == 0)
{
v___x_6529_ = v___x_6526_;
v_isShared_6530_ = v_isSharedCheck_6534_;
goto v_resetjp_6528_;
}
else
{
lean_inc(v_a_6527_);
lean_dec(v___x_6526_);
v___x_6529_ = lean_box(0);
v_isShared_6530_ = v_isSharedCheck_6534_;
goto v_resetjp_6528_;
}
v_resetjp_6528_:
{
lean_object* v___x_6532_; 
if (v_isShared_6530_ == 0)
{
v___x_6532_ = v___x_6529_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6533_; 
v_reuseFailAlloc_6533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_a_6527_);
v___x_6532_ = v_reuseFailAlloc_6533_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
return v___x_6532_;
}
}
}
else
{
lean_object* v_a_6535_; lean_object* v___x_6537_; uint8_t v_isShared_6538_; uint8_t v_isSharedCheck_6542_; 
v_a_6535_ = lean_ctor_get(v___x_6526_, 0);
v_isSharedCheck_6542_ = !lean_is_exclusive(v___x_6526_);
if (v_isSharedCheck_6542_ == 0)
{
v___x_6537_ = v___x_6526_;
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
else
{
lean_inc(v_a_6535_);
lean_dec(v___x_6526_);
v___x_6537_ = lean_box(0);
v_isShared_6538_ = v_isSharedCheck_6542_;
goto v_resetjp_6536_;
}
v_resetjp_6536_:
{
lean_object* v___x_6540_; 
if (v_isShared_6538_ == 0)
{
v___x_6540_ = v___x_6537_;
goto v_reusejp_6539_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v_a_6535_);
v___x_6540_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6539_;
}
v_reusejp_6539_:
{
return v___x_6540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___boxed(lean_object* v___x_6543_, lean_object* v_enumName_6544_, lean_object* v_a_6545_, lean_object* v___x_6546_, lean_object* v_val_6547_, lean_object* v___x_6548_, lean_object* v___x_6549_, lean_object* v_name_6550_, lean_object* v_bi_6551_, lean_object* v_type_6552_, lean_object* v_kind_6553_, lean_object* v___y_6554_, lean_object* v___y_6555_, lean_object* v___y_6556_, lean_object* v___y_6557_, lean_object* v___y_6558_){
_start:
{
uint8_t v_bi_boxed_6559_; uint8_t v_kind_boxed_6560_; lean_object* v_res_6561_; 
v_bi_boxed_6559_ = lean_unbox(v_bi_6551_);
v_kind_boxed_6560_ = lean_unbox(v_kind_6553_);
v_res_6561_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6543_, v_enumName_6544_, v_a_6545_, v___x_6546_, v_val_6547_, v___x_6548_, v___x_6549_, v_name_6550_, v_bi_boxed_6559_, v_type_6552_, v_kind_boxed_6560_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_);
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6555_);
lean_dec_ref(v___y_6554_);
return v_res_6561_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1(void){
_start:
{
lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; 
v___x_6563_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_6564_ = lean_unsigned_to_nat(63u);
v___x_6565_ = lean_unsigned_to_nat(402u);
v___x_6566_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0));
v___x_6567_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_6568_ = l_mkPanicMessageWithDecl(v___x_6567_, v___x_6566_, v___x_6565_, v___x_6564_, v___x_6563_);
return v___x_6568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(lean_object* v_enumName_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_){
_start:
{
lean_object* v___x_6575_; 
lean_inc(v_enumName_6569_);
v___x_6575_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_6569_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
if (lean_obj_tag(v___x_6575_) == 0)
{
lean_object* v_a_6576_; 
v_a_6576_ = lean_ctor_get(v___x_6575_, 0);
lean_inc(v_a_6576_);
lean_dec_ref_known(v___x_6575_, 1);
if (lean_obj_tag(v_a_6576_) == 5)
{
lean_object* v_val_6577_; lean_object* v_toConstantVal_6578_; lean_object* v_levelParams_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; 
v_val_6577_ = lean_ctor_get(v_a_6576_, 0);
lean_inc_ref(v_val_6577_);
lean_dec_ref_known(v_a_6576_, 1);
v_toConstantVal_6578_ = lean_ctor_get(v_val_6577_, 0);
v_levelParams_6579_ = lean_ctor_get(v_toConstantVal_6578_, 1);
lean_inc_n(v_levelParams_6579_, 2);
v___x_6580_ = lean_box(0);
v___x_6581_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_6579_, v___x_6580_);
v___x_6582_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_6583_ = l_Lean_Core_mkFreshUserName(v___x_6582_, v_a_6572_, v_a_6573_);
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; uint8_t v___x_6595_; uint8_t v___x_6596_; lean_object* v___x_6597_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
lean_inc_n(v_a_6584_, 2);
lean_dec_ref_known(v___x_6583_, 1);
lean_inc_n(v___x_6581_, 2);
lean_inc_n(v_enumName_6569_, 3);
v___x_6585_ = l_Lean_mkConst(v_enumName_6569_, v___x_6581_);
v___x_6586_ = l_Lean_mkLevelParam(v_a_6584_);
lean_inc(v___x_6586_);
v___x_6587_ = l_Lean_mkSort(v___x_6586_);
v___x_6588_ = l_Lean_mkCtorIdxName(v_enumName_6569_);
v___x_6589_ = l_Lean_mkConst(v___x_6588_, v___x_6581_);
v___x_6590_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_6591_ = l_Lean_Name_str___override(v_enumName_6569_, v___x_6590_);
v___x_6592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6592_, 0, v___x_6586_);
lean_ctor_set(v___x_6592_, 1, v___x_6581_);
v___x_6593_ = l_Lean_mkConst(v___x_6591_, v___x_6592_);
v___x_6594_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_6595_ = 1;
v___x_6596_ = 0;
v___x_6597_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6593_, v_enumName_6569_, v_a_6584_, v_levelParams_6579_, v_val_6577_, v___x_6589_, v___x_6585_, v___x_6594_, v___x_6595_, v___x_6587_, v___x_6596_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
return v___x_6597_;
}
else
{
lean_object* v_a_6598_; lean_object* v___x_6600_; uint8_t v_isShared_6601_; uint8_t v_isSharedCheck_6605_; 
lean_dec(v___x_6581_);
lean_dec(v_levelParams_6579_);
lean_dec_ref(v_val_6577_);
lean_dec(v_enumName_6569_);
v_a_6598_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6605_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6605_ == 0)
{
v___x_6600_ = v___x_6583_;
v_isShared_6601_ = v_isSharedCheck_6605_;
goto v_resetjp_6599_;
}
else
{
lean_inc(v_a_6598_);
lean_dec(v___x_6583_);
v___x_6600_ = lean_box(0);
v_isShared_6601_ = v_isSharedCheck_6605_;
goto v_resetjp_6599_;
}
v_resetjp_6599_:
{
lean_object* v___x_6603_; 
if (v_isShared_6601_ == 0)
{
v___x_6603_ = v___x_6600_;
goto v_reusejp_6602_;
}
else
{
lean_object* v_reuseFailAlloc_6604_; 
v_reuseFailAlloc_6604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_a_6598_);
v___x_6603_ = v_reuseFailAlloc_6604_;
goto v_reusejp_6602_;
}
v_reusejp_6602_:
{
return v___x_6603_;
}
}
}
}
else
{
lean_object* v___x_6606_; lean_object* v___x_6607_; 
lean_dec(v_a_6576_);
lean_dec(v_enumName_6569_);
v___x_6606_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1);
v___x_6607_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_6606_, v_a_6570_, v_a_6571_, v_a_6572_, v_a_6573_);
return v___x_6607_;
}
}
else
{
lean_object* v_a_6608_; lean_object* v___x_6610_; uint8_t v_isShared_6611_; uint8_t v_isSharedCheck_6615_; 
lean_dec(v_enumName_6569_);
v_a_6608_ = lean_ctor_get(v___x_6575_, 0);
v_isSharedCheck_6615_ = !lean_is_exclusive(v___x_6575_);
if (v_isSharedCheck_6615_ == 0)
{
v___x_6610_ = v___x_6575_;
v_isShared_6611_ = v_isSharedCheck_6615_;
goto v_resetjp_6609_;
}
else
{
lean_inc(v_a_6608_);
lean_dec(v___x_6575_);
v___x_6610_ = lean_box(0);
v_isShared_6611_ = v_isSharedCheck_6615_;
goto v_resetjp_6609_;
}
v_resetjp_6609_:
{
lean_object* v___x_6613_; 
if (v_isShared_6611_ == 0)
{
v___x_6613_ = v___x_6610_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6608_);
v___x_6613_ = v_reuseFailAlloc_6614_;
goto v_reusejp_6612_;
}
v_reusejp_6612_:
{
return v___x_6613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___boxed(lean_object* v_enumName_6616_, lean_object* v_a_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_){
_start:
{
lean_object* v_res_6622_; 
v_res_6622_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6616_, v_a_6617_, v_a_6618_, v_a_6619_, v_a_6620_);
lean_dec(v_a_6620_);
lean_dec_ref(v_a_6619_);
lean_dec(v_a_6618_);
lean_dec_ref(v_a_6617_);
return v_res_6622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(lean_object* v_enumName_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_, lean_object* v_a_6627_){
_start:
{
lean_object* v___x_6629_; lean_object* v_env_6630_; lean_object* v___x_6631_; uint8_t v___y_6633_; lean_object* v___x_6637_; uint8_t v___x_6638_; uint8_t v___x_6639_; 
v___x_6629_ = lean_st_ref_get(v_a_6627_);
v_env_6630_ = lean_ctor_get(v___x_6629_, 0);
lean_inc_ref(v_env_6630_);
lean_dec(v___x_6629_);
v___x_6631_ = lean_st_ref_get(v_a_6627_);
v___x_6637_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6638_ = 1;
v___x_6639_ = l_Lean_Environment_contains(v_env_6630_, v___x_6637_, v___x_6638_);
if (v___x_6639_ == 0)
{
lean_dec(v___x_6631_);
v___y_6633_ = v___x_6639_;
goto v___jp_6632_;
}
else
{
lean_object* v_env_6640_; lean_object* v___x_6641_; uint8_t v___x_6642_; 
v_env_6640_ = lean_ctor_get(v___x_6631_, 0);
lean_inc_ref(v_env_6640_);
lean_dec(v___x_6631_);
lean_inc(v_enumName_6623_);
v___x_6641_ = l_Lean_mkCtorIdxName(v_enumName_6623_);
v___x_6642_ = l_Lean_Environment_contains(v_env_6640_, v___x_6641_, v___x_6639_);
v___y_6633_ = v___x_6642_;
goto v___jp_6632_;
}
v___jp_6632_:
{
if (v___y_6633_ == 0)
{
lean_object* v___x_6634_; 
v___x_6634_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_enumName_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
return v___x_6634_;
}
else
{
lean_object* v___x_6635_; 
lean_inc(v_enumName_6623_);
v___x_6635_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
if (lean_obj_tag(v___x_6635_) == 0)
{
lean_object* v___x_6636_; 
lean_dec_ref_known(v___x_6635_, 1);
v___x_6636_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6623_, v_a_6624_, v_a_6625_, v_a_6626_, v_a_6627_);
return v___x_6636_;
}
else
{
lean_dec(v_enumName_6623_);
return v___x_6635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum___boxed(lean_object* v_enumName_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_){
_start:
{
lean_object* v_res_6649_; 
v_res_6649_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_enumName_6643_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_);
lean_dec(v_a_6647_);
lean_dec_ref(v_a_6646_);
lean_dec(v_a_6645_);
lean_dec_ref(v_a_6644_);
return v_res_6649_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; 
v___x_6650_ = lean_unsigned_to_nat(32u);
v___x_6651_ = lean_mk_empty_array_with_capacity(v___x_6650_);
v___x_6652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6652_, 0, v___x_6651_);
return v___x_6652_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; 
v___x_6653_ = ((size_t)5ULL);
v___x_6654_ = lean_unsigned_to_nat(0u);
v___x_6655_ = lean_unsigned_to_nat(32u);
v___x_6656_ = lean_mk_empty_array_with_capacity(v___x_6655_);
v___x_6657_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0);
v___x_6658_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6658_, 0, v___x_6657_);
lean_ctor_set(v___x_6658_, 1, v___x_6656_);
lean_ctor_set(v___x_6658_, 2, v___x_6654_);
lean_ctor_set(v___x_6658_, 3, v___x_6654_);
lean_ctor_set_usize(v___x_6658_, 4, v___x_6653_);
return v___x_6658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(lean_object* v___y_6659_){
_start:
{
lean_object* v___x_6661_; lean_object* v_traceState_6662_; lean_object* v_traces_6663_; lean_object* v___x_6664_; lean_object* v_traceState_6665_; lean_object* v_env_6666_; lean_object* v_nextMacroScope_6667_; lean_object* v_ngen_6668_; lean_object* v_auxDeclNGen_6669_; lean_object* v_cache_6670_; lean_object* v_messages_6671_; lean_object* v_infoState_6672_; lean_object* v_snapshotTasks_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6692_; 
v___x_6661_ = lean_st_ref_get(v___y_6659_);
v_traceState_6662_ = lean_ctor_get(v___x_6661_, 4);
lean_inc_ref(v_traceState_6662_);
lean_dec(v___x_6661_);
v_traces_6663_ = lean_ctor_get(v_traceState_6662_, 0);
lean_inc_ref(v_traces_6663_);
lean_dec_ref(v_traceState_6662_);
v___x_6664_ = lean_st_ref_take(v___y_6659_);
v_traceState_6665_ = lean_ctor_get(v___x_6664_, 4);
v_env_6666_ = lean_ctor_get(v___x_6664_, 0);
v_nextMacroScope_6667_ = lean_ctor_get(v___x_6664_, 1);
v_ngen_6668_ = lean_ctor_get(v___x_6664_, 2);
v_auxDeclNGen_6669_ = lean_ctor_get(v___x_6664_, 3);
v_cache_6670_ = lean_ctor_get(v___x_6664_, 5);
v_messages_6671_ = lean_ctor_get(v___x_6664_, 6);
v_infoState_6672_ = lean_ctor_get(v___x_6664_, 7);
v_snapshotTasks_6673_ = lean_ctor_get(v___x_6664_, 8);
v_isSharedCheck_6692_ = !lean_is_exclusive(v___x_6664_);
if (v_isSharedCheck_6692_ == 0)
{
v___x_6675_ = v___x_6664_;
v_isShared_6676_ = v_isSharedCheck_6692_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_snapshotTasks_6673_);
lean_inc(v_infoState_6672_);
lean_inc(v_messages_6671_);
lean_inc(v_cache_6670_);
lean_inc(v_traceState_6665_);
lean_inc(v_auxDeclNGen_6669_);
lean_inc(v_ngen_6668_);
lean_inc(v_nextMacroScope_6667_);
lean_inc(v_env_6666_);
lean_dec(v___x_6664_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6692_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
uint64_t v_tid_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6690_; 
v_tid_6677_ = lean_ctor_get_uint64(v_traceState_6665_, sizeof(void*)*1);
v_isSharedCheck_6690_ = !lean_is_exclusive(v_traceState_6665_);
if (v_isSharedCheck_6690_ == 0)
{
lean_object* v_unused_6691_; 
v_unused_6691_ = lean_ctor_get(v_traceState_6665_, 0);
lean_dec(v_unused_6691_);
v___x_6679_ = v_traceState_6665_;
v_isShared_6680_ = v_isSharedCheck_6690_;
goto v_resetjp_6678_;
}
else
{
lean_dec(v_traceState_6665_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6690_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___x_6681_; lean_object* v___x_6683_; 
v___x_6681_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6681_);
v___x_6683_ = v___x_6679_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v___x_6681_);
lean_ctor_set_uint64(v_reuseFailAlloc_6689_, sizeof(void*)*1, v_tid_6677_);
v___x_6683_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
lean_object* v___x_6685_; 
if (v_isShared_6676_ == 0)
{
lean_ctor_set(v___x_6675_, 4, v___x_6683_);
v___x_6685_ = v___x_6675_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6688_; 
v_reuseFailAlloc_6688_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6688_, 0, v_env_6666_);
lean_ctor_set(v_reuseFailAlloc_6688_, 1, v_nextMacroScope_6667_);
lean_ctor_set(v_reuseFailAlloc_6688_, 2, v_ngen_6668_);
lean_ctor_set(v_reuseFailAlloc_6688_, 3, v_auxDeclNGen_6669_);
lean_ctor_set(v_reuseFailAlloc_6688_, 4, v___x_6683_);
lean_ctor_set(v_reuseFailAlloc_6688_, 5, v_cache_6670_);
lean_ctor_set(v_reuseFailAlloc_6688_, 6, v_messages_6671_);
lean_ctor_set(v_reuseFailAlloc_6688_, 7, v_infoState_6672_);
lean_ctor_set(v_reuseFailAlloc_6688_, 8, v_snapshotTasks_6673_);
v___x_6685_ = v_reuseFailAlloc_6688_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
lean_object* v___x_6686_; lean_object* v___x_6687_; 
v___x_6686_ = lean_st_ref_put(v___y_6659_, v___x_6685_);
v___x_6687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6687_, 0, v_traces_6663_);
return v___x_6687_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___boxed(lean_object* v___y_6693_, lean_object* v___y_6694_){
_start:
{
lean_object* v_res_6695_; 
v_res_6695_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6693_);
lean_dec(v___y_6693_);
return v_res_6695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(lean_object* v___y_6696_, lean_object* v___y_6697_, lean_object* v___y_6698_, lean_object* v___y_6699_){
_start:
{
lean_object* v___x_6701_; 
v___x_6701_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6699_);
return v___x_6701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___boxed(lean_object* v___y_6702_, lean_object* v___y_6703_, lean_object* v___y_6704_, lean_object* v___y_6705_, lean_object* v___y_6706_){
_start:
{
lean_object* v_res_6707_; 
v_res_6707_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
lean_dec(v___y_6705_);
lean_dec_ref(v___y_6704_);
lean_dec(v___y_6703_);
lean_dec_ref(v___y_6702_);
return v_res_6707_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0(lean_object* v_declName_6708_, lean_object* v_x_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_, lean_object* v___y_6712_, lean_object* v___y_6713_){
_start:
{
lean_object* v___x_6715_; lean_object* v___x_6716_; 
v___x_6715_ = l_Lean_MessageData_ofName(v_declName_6708_);
v___x_6716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6716_, 0, v___x_6715_);
return v___x_6716_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0___boxed(lean_object* v_declName_6717_, lean_object* v_x_6718_, lean_object* v___y_6719_, lean_object* v___y_6720_, lean_object* v___y_6721_, lean_object* v___y_6722_, lean_object* v___y_6723_){
_start:
{
lean_object* v_res_6724_; 
v_res_6724_ = l_Lean_mkNoConfusion___lam__0(v_declName_6717_, v_x_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_);
lean_dec(v___y_6722_);
lean_dec_ref(v___y_6721_);
lean_dec(v___y_6720_);
lean_dec_ref(v___y_6719_);
lean_dec_ref(v_x_6718_);
return v_res_6724_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(uint8_t v___x_6725_, lean_object* v_x_6726_, lean_object* v___y_6727_, lean_object* v___y_6728_, lean_object* v___y_6729_, lean_object* v___y_6730_){
_start:
{
if (lean_obj_tag(v_x_6726_) == 0)
{
uint8_t v___x_6732_; lean_object* v___x_6733_; lean_object* v___x_6734_; 
v___x_6732_ = 1;
v___x_6733_ = lean_box(v___x_6732_);
v___x_6734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6734_, 0, v___x_6733_);
return v___x_6734_;
}
else
{
lean_object* v_head_6735_; lean_object* v_tail_6736_; lean_object* v___y_6738_; uint8_t v_a_6739_; lean_object* v___x_6741_; lean_object* v___x_6742_; 
v_head_6735_ = lean_ctor_get(v_x_6726_, 0);
lean_inc(v_head_6735_);
v_tail_6736_ = lean_ctor_get(v_x_6726_, 1);
lean_inc(v_tail_6736_);
lean_dec_ref_known(v_x_6726_, 2);
v___x_6741_ = lean_unsigned_to_nat(0u);
v___x_6742_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_head_6735_, v___y_6727_, v___y_6728_, v___y_6729_, v___y_6730_);
if (lean_obj_tag(v___x_6742_) == 0)
{
lean_object* v_a_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6758_; 
v_a_6743_ = lean_ctor_get(v___x_6742_, 0);
v_isSharedCheck_6758_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6758_ == 0)
{
v___x_6745_ = v___x_6742_;
v_isShared_6746_ = v_isSharedCheck_6758_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_a_6743_);
lean_dec(v___x_6742_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6758_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
if (lean_obj_tag(v_a_6743_) == 6)
{
lean_object* v_val_6747_; lean_object* v_numFields_6748_; uint8_t v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6752_; 
v_val_6747_ = lean_ctor_get(v_a_6743_, 0);
lean_inc_ref(v_val_6747_);
lean_dec_ref_known(v_a_6743_, 1);
v_numFields_6748_ = lean_ctor_get(v_val_6747_, 4);
lean_inc(v_numFields_6748_);
lean_dec_ref(v_val_6747_);
v___x_6749_ = lean_nat_dec_eq(v_numFields_6748_, v___x_6741_);
lean_dec(v_numFields_6748_);
v___x_6750_ = lean_box(v___x_6749_);
if (v_isShared_6746_ == 0)
{
lean_ctor_set(v___x_6745_, 0, v___x_6750_);
v___x_6752_ = v___x_6745_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v___x_6750_);
v___x_6752_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
v___y_6738_ = v___x_6752_;
v_a_6739_ = v___x_6749_;
goto v___jp_6737_;
}
}
else
{
lean_object* v___x_6754_; lean_object* v___x_6756_; 
lean_dec(v_a_6743_);
v___x_6754_ = lean_box(v___x_6725_);
if (v_isShared_6746_ == 0)
{
lean_ctor_set(v___x_6745_, 0, v___x_6754_);
v___x_6756_ = v___x_6745_;
goto v_reusejp_6755_;
}
else
{
lean_object* v_reuseFailAlloc_6757_; 
v_reuseFailAlloc_6757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6757_, 0, v___x_6754_);
v___x_6756_ = v_reuseFailAlloc_6757_;
goto v_reusejp_6755_;
}
v_reusejp_6755_:
{
v___y_6738_ = v___x_6756_;
v_a_6739_ = v___x_6725_;
goto v___jp_6737_;
}
}
}
}
else
{
lean_object* v_a_6759_; lean_object* v___x_6761_; uint8_t v_isShared_6762_; uint8_t v_isSharedCheck_6766_; 
lean_dec(v_tail_6736_);
v_a_6759_ = lean_ctor_get(v___x_6742_, 0);
v_isSharedCheck_6766_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6766_ == 0)
{
v___x_6761_ = v___x_6742_;
v_isShared_6762_ = v_isSharedCheck_6766_;
goto v_resetjp_6760_;
}
else
{
lean_inc(v_a_6759_);
lean_dec(v___x_6742_);
v___x_6761_ = lean_box(0);
v_isShared_6762_ = v_isSharedCheck_6766_;
goto v_resetjp_6760_;
}
v_resetjp_6760_:
{
lean_object* v___x_6764_; 
if (v_isShared_6762_ == 0)
{
v___x_6764_ = v___x_6761_;
goto v_reusejp_6763_;
}
else
{
lean_object* v_reuseFailAlloc_6765_; 
v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6759_);
v___x_6764_ = v_reuseFailAlloc_6765_;
goto v_reusejp_6763_;
}
v_reusejp_6763_:
{
return v___x_6764_;
}
}
}
v___jp_6737_:
{
if (v_a_6739_ == 0)
{
lean_dec(v_tail_6736_);
return v___y_6738_;
}
else
{
lean_dec_ref(v___y_6738_);
v_x_6726_ = v_tail_6736_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0___boxed(lean_object* v___x_6767_, lean_object* v_x_6768_, lean_object* v___y_6769_, lean_object* v___y_6770_, lean_object* v___y_6771_, lean_object* v___y_6772_, lean_object* v___y_6773_){
_start:
{
uint8_t v___x_8116__boxed_6774_; lean_object* v_res_6775_; 
v___x_8116__boxed_6774_ = lean_unbox(v___x_6767_);
v_res_6775_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v___x_8116__boxed_6774_, v_x_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
lean_dec(v___y_6772_);
lean_dec_ref(v___y_6771_);
lean_dec(v___y_6770_);
lean_dec_ref(v___y_6769_);
return v_res_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(lean_object* v_declName_6776_, lean_object* v___y_6777_, lean_object* v___y_6778_, lean_object* v___y_6779_, lean_object* v___y_6780_){
_start:
{
lean_object* v___x_6782_; 
v___x_6782_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_6776_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_);
if (lean_obj_tag(v___x_6782_) == 0)
{
lean_object* v_a_6783_; lean_object* v___x_6785_; uint8_t v_isShared_6786_; uint8_t v_isSharedCheck_6838_; 
v_a_6783_ = lean_ctor_get(v___x_6782_, 0);
v_isSharedCheck_6838_ = !lean_is_exclusive(v___x_6782_);
if (v_isSharedCheck_6838_ == 0)
{
v___x_6785_ = v___x_6782_;
v_isShared_6786_ = v_isSharedCheck_6838_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_a_6783_);
lean_dec(v___x_6782_);
v___x_6785_ = lean_box(0);
v_isShared_6786_ = v_isSharedCheck_6838_;
goto v_resetjp_6784_;
}
v_resetjp_6784_:
{
if (lean_obj_tag(v_a_6783_) == 5)
{
lean_object* v_val_6787_; lean_object* v_toConstantVal_6788_; lean_object* v_numParams_6789_; lean_object* v_numIndices_6790_; lean_object* v_ctors_6791_; uint8_t v_isRec_6792_; uint8_t v_isUnsafe_6793_; lean_object* v_type_6794_; uint8_t v___x_6795_; 
v_val_6787_ = lean_ctor_get(v_a_6783_, 0);
lean_inc_ref(v_val_6787_);
lean_dec_ref_known(v_a_6783_, 1);
v_toConstantVal_6788_ = lean_ctor_get(v_val_6787_, 0);
v_numParams_6789_ = lean_ctor_get(v_val_6787_, 1);
lean_inc(v_numParams_6789_);
v_numIndices_6790_ = lean_ctor_get(v_val_6787_, 2);
lean_inc(v_numIndices_6790_);
v_ctors_6791_ = lean_ctor_get(v_val_6787_, 4);
lean_inc(v_ctors_6791_);
v_isRec_6792_ = lean_ctor_get_uint8(v_val_6787_, sizeof(void*)*6);
v_isUnsafe_6793_ = lean_ctor_get_uint8(v_val_6787_, sizeof(void*)*6 + 1);
v_type_6794_ = lean_ctor_get(v_toConstantVal_6788_, 2);
v___x_6795_ = l_Lean_Expr_isProp(v_type_6794_);
if (v___x_6795_ == 0)
{
lean_object* v___x_6796_; lean_object* v___x_6797_; uint8_t v___x_6798_; 
v___x_6796_ = l_Lean_InductiveVal_numTypeFormers(v_val_6787_);
lean_dec_ref(v_val_6787_);
v___x_6797_ = lean_unsigned_to_nat(1u);
v___x_6798_ = lean_nat_dec_eq(v___x_6796_, v___x_6797_);
lean_dec(v___x_6796_);
if (v___x_6798_ == 0)
{
lean_object* v___x_6799_; lean_object* v___x_6801_; 
lean_dec(v_ctors_6791_);
lean_dec(v_numIndices_6790_);
lean_dec(v_numParams_6789_);
v___x_6799_ = lean_box(v___x_6798_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6799_);
v___x_6801_ = v___x_6785_;
goto v_reusejp_6800_;
}
else
{
lean_object* v_reuseFailAlloc_6802_; 
v_reuseFailAlloc_6802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6802_, 0, v___x_6799_);
v___x_6801_ = v_reuseFailAlloc_6802_;
goto v_reusejp_6800_;
}
v_reusejp_6800_:
{
return v___x_6801_;
}
}
else
{
lean_object* v___x_6803_; uint8_t v___x_6804_; 
v___x_6803_ = lean_unsigned_to_nat(0u);
v___x_6804_ = lean_nat_dec_eq(v_numIndices_6790_, v___x_6803_);
lean_dec(v_numIndices_6790_);
if (v___x_6804_ == 0)
{
lean_object* v___x_6805_; lean_object* v___x_6807_; 
lean_dec(v_ctors_6791_);
lean_dec(v_numParams_6789_);
v___x_6805_ = lean_box(v___x_6804_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6805_);
v___x_6807_ = v___x_6785_;
goto v_reusejp_6806_;
}
else
{
lean_object* v_reuseFailAlloc_6808_; 
v_reuseFailAlloc_6808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6808_, 0, v___x_6805_);
v___x_6807_ = v_reuseFailAlloc_6808_;
goto v_reusejp_6806_;
}
v_reusejp_6806_:
{
return v___x_6807_;
}
}
else
{
uint8_t v___x_6809_; 
v___x_6809_ = lean_nat_dec_eq(v_numParams_6789_, v___x_6803_);
lean_dec(v_numParams_6789_);
if (v___x_6809_ == 0)
{
lean_object* v___x_6810_; lean_object* v___x_6812_; 
lean_dec(v_ctors_6791_);
v___x_6810_ = lean_box(v___x_6809_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6810_);
v___x_6812_ = v___x_6785_;
goto v_reusejp_6811_;
}
else
{
lean_object* v_reuseFailAlloc_6813_; 
v_reuseFailAlloc_6813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6813_, 0, v___x_6810_);
v___x_6812_ = v_reuseFailAlloc_6813_;
goto v_reusejp_6811_;
}
v_reusejp_6811_:
{
return v___x_6812_;
}
}
else
{
uint8_t v___x_6814_; 
v___x_6814_ = l_List_isEmpty___redArg(v_ctors_6791_);
if (v___x_6814_ == 0)
{
if (v_isRec_6792_ == 0)
{
if (v_isUnsafe_6793_ == 0)
{
lean_object* v___x_6815_; 
lean_del_object(v___x_6785_);
v___x_6815_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v_isUnsafe_6793_, v_ctors_6791_, v___y_6777_, v___y_6778_, v___y_6779_, v___y_6780_);
return v___x_6815_;
}
else
{
lean_object* v___x_6816_; lean_object* v___x_6818_; 
lean_dec(v_ctors_6791_);
v___x_6816_ = lean_box(v_isRec_6792_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6816_);
v___x_6818_ = v___x_6785_;
goto v_reusejp_6817_;
}
else
{
lean_object* v_reuseFailAlloc_6819_; 
v_reuseFailAlloc_6819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6819_, 0, v___x_6816_);
v___x_6818_ = v_reuseFailAlloc_6819_;
goto v_reusejp_6817_;
}
v_reusejp_6817_:
{
return v___x_6818_;
}
}
}
else
{
lean_object* v___x_6820_; lean_object* v___x_6822_; 
lean_dec(v_ctors_6791_);
v___x_6820_ = lean_box(v___x_6814_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6820_);
v___x_6822_ = v___x_6785_;
goto v_reusejp_6821_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v___x_6820_);
v___x_6822_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6821_;
}
v_reusejp_6821_:
{
return v___x_6822_;
}
}
}
else
{
lean_object* v___x_6824_; lean_object* v___x_6826_; 
lean_dec(v_ctors_6791_);
v___x_6824_ = lean_box(v___x_6795_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6824_);
v___x_6826_ = v___x_6785_;
goto v_reusejp_6825_;
}
else
{
lean_object* v_reuseFailAlloc_6827_; 
v_reuseFailAlloc_6827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6827_, 0, v___x_6824_);
v___x_6826_ = v_reuseFailAlloc_6827_;
goto v_reusejp_6825_;
}
v_reusejp_6825_:
{
return v___x_6826_;
}
}
}
}
}
}
else
{
uint8_t v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6831_; 
lean_dec(v_ctors_6791_);
lean_dec(v_numIndices_6790_);
lean_dec(v_numParams_6789_);
lean_dec_ref(v_val_6787_);
v___x_6828_ = 0;
v___x_6829_ = lean_box(v___x_6828_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6829_);
v___x_6831_ = v___x_6785_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v___x_6829_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
return v___x_6831_;
}
}
}
else
{
uint8_t v___x_6833_; lean_object* v___x_6834_; lean_object* v___x_6836_; 
lean_dec(v_a_6783_);
v___x_6833_ = 0;
v___x_6834_ = lean_box(v___x_6833_);
if (v_isShared_6786_ == 0)
{
lean_ctor_set(v___x_6785_, 0, v___x_6834_);
v___x_6836_ = v___x_6785_;
goto v_reusejp_6835_;
}
else
{
lean_object* v_reuseFailAlloc_6837_; 
v_reuseFailAlloc_6837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6837_, 0, v___x_6834_);
v___x_6836_ = v_reuseFailAlloc_6837_;
goto v_reusejp_6835_;
}
v_reusejp_6835_:
{
return v___x_6836_;
}
}
}
}
else
{
lean_object* v_a_6839_; lean_object* v___x_6841_; uint8_t v_isShared_6842_; uint8_t v_isSharedCheck_6846_; 
v_a_6839_ = lean_ctor_get(v___x_6782_, 0);
v_isSharedCheck_6846_ = !lean_is_exclusive(v___x_6782_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6841_ = v___x_6782_;
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
else
{
lean_inc(v_a_6839_);
lean_dec(v___x_6782_);
v___x_6841_ = lean_box(0);
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
v_resetjp_6840_:
{
lean_object* v___x_6844_; 
if (v_isShared_6842_ == 0)
{
v___x_6844_ = v___x_6841_;
goto v_reusejp_6843_;
}
else
{
lean_object* v_reuseFailAlloc_6845_; 
v_reuseFailAlloc_6845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6845_, 0, v_a_6839_);
v___x_6844_ = v_reuseFailAlloc_6845_;
goto v_reusejp_6843_;
}
v_reusejp_6843_:
{
return v___x_6844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0___boxed(lean_object* v_declName_6847_, lean_object* v___y_6848_, lean_object* v___y_6849_, lean_object* v___y_6850_, lean_object* v___y_6851_, lean_object* v___y_6852_){
_start:
{
lean_object* v_res_6853_; 
v_res_6853_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_6847_, v___y_6848_, v___y_6849_, v___y_6850_, v___y_6851_);
lean_dec(v___y_6851_);
lean_dec_ref(v___y_6850_);
lean_dec(v___y_6849_);
lean_dec_ref(v___y_6848_);
return v_res_6853_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(lean_object* v_x_6854_){
_start:
{
if (lean_obj_tag(v_x_6854_) == 0)
{
lean_object* v_a_6856_; lean_object* v___x_6858_; uint8_t v_isShared_6859_; uint8_t v_isSharedCheck_6863_; 
v_a_6856_ = lean_ctor_get(v_x_6854_, 0);
v_isSharedCheck_6863_ = !lean_is_exclusive(v_x_6854_);
if (v_isSharedCheck_6863_ == 0)
{
v___x_6858_ = v_x_6854_;
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
else
{
lean_inc(v_a_6856_);
lean_dec(v_x_6854_);
v___x_6858_ = lean_box(0);
v_isShared_6859_ = v_isSharedCheck_6863_;
goto v_resetjp_6857_;
}
v_resetjp_6857_:
{
lean_object* v___x_6861_; 
if (v_isShared_6859_ == 0)
{
lean_ctor_set_tag(v___x_6858_, 1);
v___x_6861_ = v___x_6858_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6862_; 
v_reuseFailAlloc_6862_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_a_6864_; lean_object* v___x_6866_; uint8_t v_isShared_6867_; uint8_t v_isSharedCheck_6871_; 
v_a_6864_ = lean_ctor_get(v_x_6854_, 0);
v_isSharedCheck_6871_ = !lean_is_exclusive(v_x_6854_);
if (v_isSharedCheck_6871_ == 0)
{
v___x_6866_ = v_x_6854_;
v_isShared_6867_ = v_isSharedCheck_6871_;
goto v_resetjp_6865_;
}
else
{
lean_inc(v_a_6864_);
lean_dec(v_x_6854_);
v___x_6866_ = lean_box(0);
v_isShared_6867_ = v_isSharedCheck_6871_;
goto v_resetjp_6865_;
}
v_resetjp_6865_:
{
lean_object* v___x_6869_; 
if (v_isShared_6867_ == 0)
{
lean_ctor_set_tag(v___x_6866_, 0);
v___x_6869_ = v___x_6866_;
goto v_reusejp_6868_;
}
else
{
lean_object* v_reuseFailAlloc_6870_; 
v_reuseFailAlloc_6870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6870_, 0, v_a_6864_);
v___x_6869_ = v_reuseFailAlloc_6870_;
goto v_reusejp_6868_;
}
v_reusejp_6868_:
{
return v___x_6869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg___boxed(lean_object* v_x_6872_, lean_object* v___y_6873_){
_start:
{
lean_object* v_res_6874_; 
v_res_6874_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_6872_);
return v_res_6874_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(lean_object* v_e_6875_){
_start:
{
if (lean_obj_tag(v_e_6875_) == 0)
{
uint8_t v___x_6876_; 
v___x_6876_ = 2;
return v___x_6876_;
}
else
{
uint8_t v___x_6877_; 
v___x_6877_ = 0;
return v___x_6877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5___boxed(lean_object* v_e_6878_){
_start:
{
uint8_t v_res_6879_; lean_object* v_r_6880_; 
v_res_6879_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_e_6878_);
lean_dec_ref(v_e_6878_);
v_r_6880_ = lean_box(v_res_6879_);
return v_r_6880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(size_t v_sz_6881_, size_t v_i_6882_, lean_object* v_bs_6883_){
_start:
{
uint8_t v___x_6884_; 
v___x_6884_ = lean_usize_dec_lt(v_i_6882_, v_sz_6881_);
if (v___x_6884_ == 0)
{
return v_bs_6883_;
}
else
{
lean_object* v_v_6885_; lean_object* v_msg_6886_; lean_object* v___x_6887_; lean_object* v_bs_x27_6888_; size_t v___x_6889_; size_t v___x_6890_; lean_object* v___x_6891_; 
v_v_6885_ = lean_array_uget_borrowed(v_bs_6883_, v_i_6882_);
v_msg_6886_ = lean_ctor_get(v_v_6885_, 1);
lean_inc_ref(v_msg_6886_);
v___x_6887_ = lean_unsigned_to_nat(0u);
v_bs_x27_6888_ = lean_array_uset(v_bs_6883_, v_i_6882_, v___x_6887_);
v___x_6889_ = ((size_t)1ULL);
v___x_6890_ = lean_usize_add(v_i_6882_, v___x_6889_);
v___x_6891_ = lean_array_uset(v_bs_x27_6888_, v_i_6882_, v_msg_6886_);
v_i_6882_ = v___x_6890_;
v_bs_6883_ = v___x_6891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_6893_, lean_object* v_i_6894_, lean_object* v_bs_6895_){
_start:
{
size_t v_sz_boxed_6896_; size_t v_i_boxed_6897_; lean_object* v_res_6898_; 
v_sz_boxed_6896_ = lean_unbox_usize(v_sz_6893_);
lean_dec(v_sz_6893_);
v_i_boxed_6897_ = lean_unbox_usize(v_i_6894_);
lean_dec(v_i_6894_);
v_res_6898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_boxed_6896_, v_i_boxed_6897_, v_bs_6895_);
return v_res_6898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(lean_object* v_oldTraces_6899_, lean_object* v_data_6900_, lean_object* v_ref_6901_, lean_object* v_msg_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_, lean_object* v___y_6905_, lean_object* v___y_6906_){
_start:
{
lean_object* v_toCold_6908_; lean_object* v_currRecDepth_6909_; lean_object* v_ref_6910_; uint8_t v_diag_6911_; uint8_t v_suppressElabErrors_6912_; lean_object* v_ref_6913_; lean_object* v___x_6914_; lean_object* v___x_6915_; lean_object* v_traceState_6916_; lean_object* v_traces_6917_; lean_object* v___x_6918_; size_t v_sz_6919_; size_t v___x_6920_; lean_object* v___x_6921_; lean_object* v_msg_6922_; lean_object* v___x_6923_; lean_object* v_a_6924_; lean_object* v___x_6926_; uint8_t v_isShared_6927_; uint8_t v_isSharedCheck_6961_; 
v_toCold_6908_ = lean_ctor_get(v___y_6905_, 0);
v_currRecDepth_6909_ = lean_ctor_get(v___y_6905_, 1);
v_ref_6910_ = lean_ctor_get(v___y_6905_, 2);
v_diag_6911_ = lean_ctor_get_uint8(v___y_6905_, sizeof(void*)*3);
v_suppressElabErrors_6912_ = lean_ctor_get_uint8(v___y_6905_, sizeof(void*)*3 + 1);
v_ref_6913_ = l_Lean_replaceRef(v_ref_6901_, v_ref_6910_);
lean_inc(v_currRecDepth_6909_);
lean_inc_ref(v_toCold_6908_);
v___x_6914_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_6914_, 0, v_toCold_6908_);
lean_ctor_set(v___x_6914_, 1, v_currRecDepth_6909_);
lean_ctor_set(v___x_6914_, 2, v_ref_6913_);
lean_ctor_set_uint8(v___x_6914_, sizeof(void*)*3, v_diag_6911_);
lean_ctor_set_uint8(v___x_6914_, sizeof(void*)*3 + 1, v_suppressElabErrors_6912_);
v___x_6915_ = lean_st_ref_get(v___y_6906_);
v_traceState_6916_ = lean_ctor_get(v___x_6915_, 4);
lean_inc_ref(v_traceState_6916_);
lean_dec(v___x_6915_);
v_traces_6917_ = lean_ctor_get(v_traceState_6916_, 0);
lean_inc_ref(v_traces_6917_);
lean_dec_ref(v_traceState_6916_);
v___x_6918_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6917_);
lean_dec_ref(v_traces_6917_);
v_sz_6919_ = lean_array_size(v___x_6918_);
v___x_6920_ = ((size_t)0ULL);
v___x_6921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_6919_, v___x_6920_, v___x_6918_);
v_msg_6922_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6922_, 0, v_data_6900_);
lean_ctor_set(v_msg_6922_, 1, v_msg_6902_);
lean_ctor_set(v_msg_6922_, 2, v___x_6921_);
v___x_6923_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_6922_, v___y_6903_, v___y_6904_, v___x_6914_, v___y_6906_);
lean_dec_ref_known(v___x_6914_, 3);
v_a_6924_ = lean_ctor_get(v___x_6923_, 0);
v_isSharedCheck_6961_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6961_ == 0)
{
v___x_6926_ = v___x_6923_;
v_isShared_6927_ = v_isSharedCheck_6961_;
goto v_resetjp_6925_;
}
else
{
lean_inc(v_a_6924_);
lean_dec(v___x_6923_);
v___x_6926_ = lean_box(0);
v_isShared_6927_ = v_isSharedCheck_6961_;
goto v_resetjp_6925_;
}
v_resetjp_6925_:
{
lean_object* v___x_6928_; lean_object* v_traceState_6929_; lean_object* v_env_6930_; lean_object* v_nextMacroScope_6931_; lean_object* v_ngen_6932_; lean_object* v_auxDeclNGen_6933_; lean_object* v_cache_6934_; lean_object* v_messages_6935_; lean_object* v_infoState_6936_; lean_object* v_snapshotTasks_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6960_; 
v___x_6928_ = lean_st_ref_take(v___y_6906_);
v_traceState_6929_ = lean_ctor_get(v___x_6928_, 4);
v_env_6930_ = lean_ctor_get(v___x_6928_, 0);
v_nextMacroScope_6931_ = lean_ctor_get(v___x_6928_, 1);
v_ngen_6932_ = lean_ctor_get(v___x_6928_, 2);
v_auxDeclNGen_6933_ = lean_ctor_get(v___x_6928_, 3);
v_cache_6934_ = lean_ctor_get(v___x_6928_, 5);
v_messages_6935_ = lean_ctor_get(v___x_6928_, 6);
v_infoState_6936_ = lean_ctor_get(v___x_6928_, 7);
v_snapshotTasks_6937_ = lean_ctor_get(v___x_6928_, 8);
v_isSharedCheck_6960_ = !lean_is_exclusive(v___x_6928_);
if (v_isSharedCheck_6960_ == 0)
{
v___x_6939_ = v___x_6928_;
v_isShared_6940_ = v_isSharedCheck_6960_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_snapshotTasks_6937_);
lean_inc(v_infoState_6936_);
lean_inc(v_messages_6935_);
lean_inc(v_cache_6934_);
lean_inc(v_traceState_6929_);
lean_inc(v_auxDeclNGen_6933_);
lean_inc(v_ngen_6932_);
lean_inc(v_nextMacroScope_6931_);
lean_inc(v_env_6930_);
lean_dec(v___x_6928_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6960_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
uint64_t v_tid_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6958_; 
v_tid_6941_ = lean_ctor_get_uint64(v_traceState_6929_, sizeof(void*)*1);
v_isSharedCheck_6958_ = !lean_is_exclusive(v_traceState_6929_);
if (v_isSharedCheck_6958_ == 0)
{
lean_object* v_unused_6959_; 
v_unused_6959_ = lean_ctor_get(v_traceState_6929_, 0);
lean_dec(v_unused_6959_);
v___x_6943_ = v_traceState_6929_;
v_isShared_6944_ = v_isSharedCheck_6958_;
goto v_resetjp_6942_;
}
else
{
lean_dec(v_traceState_6929_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6958_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v___x_6945_; lean_object* v___x_6946_; lean_object* v___x_6947_; lean_object* v___x_6949_; 
v___x_6945_ = lean_box(0);
v___x_6946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6946_, 0, v_ref_6901_);
lean_ctor_set(v___x_6946_, 1, v_a_6924_);
v___x_6947_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6899_, v___x_6946_);
if (v_isShared_6944_ == 0)
{
lean_ctor_set(v___x_6943_, 0, v___x_6947_);
v___x_6949_ = v___x_6943_;
goto v_reusejp_6948_;
}
else
{
lean_object* v_reuseFailAlloc_6957_; 
v_reuseFailAlloc_6957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6957_, 0, v___x_6947_);
lean_ctor_set_uint64(v_reuseFailAlloc_6957_, sizeof(void*)*1, v_tid_6941_);
v___x_6949_ = v_reuseFailAlloc_6957_;
goto v_reusejp_6948_;
}
v_reusejp_6948_:
{
lean_object* v___x_6951_; 
if (v_isShared_6940_ == 0)
{
lean_ctor_set(v___x_6939_, 4, v___x_6949_);
v___x_6951_ = v___x_6939_;
goto v_reusejp_6950_;
}
else
{
lean_object* v_reuseFailAlloc_6956_; 
v_reuseFailAlloc_6956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6956_, 0, v_env_6930_);
lean_ctor_set(v_reuseFailAlloc_6956_, 1, v_nextMacroScope_6931_);
lean_ctor_set(v_reuseFailAlloc_6956_, 2, v_ngen_6932_);
lean_ctor_set(v_reuseFailAlloc_6956_, 3, v_auxDeclNGen_6933_);
lean_ctor_set(v_reuseFailAlloc_6956_, 4, v___x_6949_);
lean_ctor_set(v_reuseFailAlloc_6956_, 5, v_cache_6934_);
lean_ctor_set(v_reuseFailAlloc_6956_, 6, v_messages_6935_);
lean_ctor_set(v_reuseFailAlloc_6956_, 7, v_infoState_6936_);
lean_ctor_set(v_reuseFailAlloc_6956_, 8, v_snapshotTasks_6937_);
v___x_6951_ = v_reuseFailAlloc_6956_;
goto v_reusejp_6950_;
}
v_reusejp_6950_:
{
lean_object* v___x_6952_; lean_object* v___x_6954_; 
v___x_6952_ = lean_st_ref_put(v___y_6906_, v___x_6951_);
if (v_isShared_6927_ == 0)
{
lean_ctor_set(v___x_6926_, 0, v___x_6945_);
v___x_6954_ = v___x_6926_;
goto v_reusejp_6953_;
}
else
{
lean_object* v_reuseFailAlloc_6955_; 
v_reuseFailAlloc_6955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6955_, 0, v___x_6945_);
v___x_6954_ = v_reuseFailAlloc_6955_;
goto v_reusejp_6953_;
}
v_reusejp_6953_:
{
return v___x_6954_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3___boxed(lean_object* v_oldTraces_6962_, lean_object* v_data_6963_, lean_object* v_ref_6964_, lean_object* v_msg_6965_, lean_object* v___y_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_){
_start:
{
lean_object* v_res_6971_; 
v_res_6971_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6962_, v_data_6963_, v_ref_6964_, v_msg_6965_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_);
lean_dec(v___y_6969_);
lean_dec_ref(v___y_6968_);
lean_dec(v___y_6967_);
lean_dec_ref(v___y_6966_);
return v_res_6971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(lean_object* v_opts_6972_, lean_object* v_opt_6973_){
_start:
{
lean_object* v_name_6974_; lean_object* v_defValue_6975_; lean_object* v_map_6976_; lean_object* v___x_6977_; 
v_name_6974_ = lean_ctor_get(v_opt_6973_, 0);
v_defValue_6975_ = lean_ctor_get(v_opt_6973_, 1);
v_map_6976_ = lean_ctor_get(v_opts_6972_, 0);
v___x_6977_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6976_, v_name_6974_);
if (lean_obj_tag(v___x_6977_) == 0)
{
lean_inc(v_defValue_6975_);
return v_defValue_6975_;
}
else
{
lean_object* v_val_6978_; 
v_val_6978_ = lean_ctor_get(v___x_6977_, 0);
lean_inc(v_val_6978_);
lean_dec_ref_known(v___x_6977_, 1);
if (lean_obj_tag(v_val_6978_) == 3)
{
lean_object* v_v_6979_; 
v_v_6979_ = lean_ctor_get(v_val_6978_, 0);
lean_inc(v_v_6979_);
lean_dec_ref_known(v_val_6978_, 1);
return v_v_6979_;
}
else
{
lean_dec(v_val_6978_);
lean_inc(v_defValue_6975_);
return v_defValue_6975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6___boxed(lean_object* v_opts_6980_, lean_object* v_opt_6981_){
_start:
{
lean_object* v_res_6982_; 
v_res_6982_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6980_, v_opt_6981_);
lean_dec_ref(v_opt_6981_);
lean_dec_ref(v_opts_6980_);
return v_res_6982_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1(void){
_start:
{
lean_object* v___x_6984_; lean_object* v___x_6985_; 
v___x_6984_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0));
v___x_6985_ = l_Lean_stringToMessageData(v___x_6984_);
return v___x_6985_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2(void){
_start:
{
lean_object* v___x_6986_; double v___x_6987_; 
v___x_6986_ = lean_unsigned_to_nat(1000u);
v___x_6987_ = lean_float_of_nat(v___x_6986_);
return v___x_6987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(lean_object* v_cls_6988_, uint8_t v_collapsed_6989_, lean_object* v_tag_6990_, lean_object* v_opts_6991_, uint8_t v_clsEnabled_6992_, lean_object* v_oldTraces_6993_, lean_object* v_msg_6994_, lean_object* v_resStartStop_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_){
_start:
{
lean_object* v_fst_7001_; lean_object* v_snd_7002_; lean_object* v___y_7004_; lean_object* v___y_7005_; lean_object* v_data_7006_; lean_object* v_fst_7009_; lean_object* v_snd_7010_; lean_object* v___x_7011_; uint8_t v___x_7012_; lean_object* v___y_7014_; lean_object* v_a_7015_; uint8_t v___y_7030_; double v___y_7061_; 
v_fst_7001_ = lean_ctor_get(v_resStartStop_6995_, 0);
lean_inc(v_fst_7001_);
v_snd_7002_ = lean_ctor_get(v_resStartStop_6995_, 1);
lean_inc(v_snd_7002_);
lean_dec_ref(v_resStartStop_6995_);
v_fst_7009_ = lean_ctor_get(v_snd_7002_, 0);
lean_inc(v_fst_7009_);
v_snd_7010_ = lean_ctor_get(v_snd_7002_, 1);
lean_inc(v_snd_7010_);
lean_dec(v_snd_7002_);
v___x_7011_ = l_Lean_trace_profiler;
v___x_7012_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6991_, v___x_7011_);
if (v___x_7012_ == 0)
{
v___y_7030_ = v___x_7012_;
goto v___jp_7029_;
}
else
{
lean_object* v___x_7066_; uint8_t v___x_7067_; 
v___x_7066_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7067_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6991_, v___x_7066_);
if (v___x_7067_ == 0)
{
lean_object* v___x_7068_; lean_object* v___x_7069_; double v___x_7070_; double v___x_7071_; double v___x_7072_; 
v___x_7068_ = l_Lean_trace_profiler_threshold;
v___x_7069_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6991_, v___x_7068_);
v___x_7070_ = lean_float_of_nat(v___x_7069_);
v___x_7071_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2);
v___x_7072_ = lean_float_div(v___x_7070_, v___x_7071_);
v___y_7061_ = v___x_7072_;
goto v___jp_7060_;
}
else
{
lean_object* v___x_7073_; lean_object* v___x_7074_; double v___x_7075_; 
v___x_7073_ = l_Lean_trace_profiler_threshold;
v___x_7074_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6991_, v___x_7073_);
v___x_7075_ = lean_float_of_nat(v___x_7074_);
v___y_7061_ = v___x_7075_;
goto v___jp_7060_;
}
}
v___jp_7003_:
{
lean_object* v___x_7007_; 
lean_inc(v___y_7005_);
v___x_7007_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6993_, v_data_7006_, v___y_7005_, v___y_7004_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_);
if (lean_obj_tag(v___x_7007_) == 0)
{
lean_object* v___x_7008_; 
lean_dec_ref_known(v___x_7007_, 1);
v___x_7008_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_7001_);
return v___x_7008_;
}
else
{
lean_dec(v_fst_7001_);
return v___x_7007_;
}
}
v___jp_7013_:
{
uint8_t v_result_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; double v___x_7019_; lean_object* v_data_7020_; 
v_result_7016_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_fst_7001_);
v___x_7017_ = lean_box(v_result_7016_);
v___x_7018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7018_, 0, v___x_7017_);
v___x_7019_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
lean_inc_ref(v_tag_6990_);
lean_inc_ref(v___x_7018_);
lean_inc(v_cls_6988_);
v_data_7020_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_7020_, 0, v_cls_6988_);
lean_ctor_set(v_data_7020_, 1, v___x_7018_);
lean_ctor_set(v_data_7020_, 2, v_tag_6990_);
lean_ctor_set_float(v_data_7020_, sizeof(void*)*3, v___x_7019_);
lean_ctor_set_float(v_data_7020_, sizeof(void*)*3 + 8, v___x_7019_);
lean_ctor_set_uint8(v_data_7020_, sizeof(void*)*3 + 16, v_collapsed_6989_);
if (v___x_7012_ == 0)
{
lean_dec_ref_known(v___x_7018_, 1);
lean_dec(v_snd_7010_);
lean_dec(v_fst_7009_);
lean_dec_ref(v_tag_6990_);
lean_dec(v_cls_6988_);
v___y_7004_ = v_a_7015_;
v___y_7005_ = v___y_7014_;
v_data_7006_ = v_data_7020_;
goto v___jp_7003_;
}
else
{
lean_object* v_data_7021_; double v___x_7022_; double v___x_7023_; 
lean_dec_ref_known(v_data_7020_, 3);
v_data_7021_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_7021_, 0, v_cls_6988_);
lean_ctor_set(v_data_7021_, 1, v___x_7018_);
lean_ctor_set(v_data_7021_, 2, v_tag_6990_);
v___x_7022_ = lean_unbox_float(v_fst_7009_);
lean_dec(v_fst_7009_);
lean_ctor_set_float(v_data_7021_, sizeof(void*)*3, v___x_7022_);
v___x_7023_ = lean_unbox_float(v_snd_7010_);
lean_dec(v_snd_7010_);
lean_ctor_set_float(v_data_7021_, sizeof(void*)*3 + 8, v___x_7023_);
lean_ctor_set_uint8(v_data_7021_, sizeof(void*)*3 + 16, v_collapsed_6989_);
v___y_7004_ = v_a_7015_;
v___y_7005_ = v___y_7014_;
v_data_7006_ = v_data_7021_;
goto v___jp_7003_;
}
}
v___jp_7024_:
{
lean_object* v_ref_7025_; lean_object* v___x_7026_; 
v_ref_7025_ = lean_ctor_get(v___y_6998_, 2);
lean_inc(v___y_6999_);
lean_inc_ref(v___y_6998_);
lean_inc(v___y_6997_);
lean_inc_ref(v___y_6996_);
lean_inc(v_fst_7001_);
v___x_7026_ = lean_apply_6(v_msg_6994_, v_fst_7001_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_, lean_box(0));
if (lean_obj_tag(v___x_7026_) == 0)
{
lean_object* v_a_7027_; 
v_a_7027_ = lean_ctor_get(v___x_7026_, 0);
lean_inc(v_a_7027_);
lean_dec_ref_known(v___x_7026_, 1);
v___y_7014_ = v_ref_7025_;
v_a_7015_ = v_a_7027_;
goto v___jp_7013_;
}
else
{
lean_object* v___x_7028_; 
lean_dec_ref_known(v___x_7026_, 1);
v___x_7028_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1);
v___y_7014_ = v_ref_7025_;
v_a_7015_ = v___x_7028_;
goto v___jp_7013_;
}
}
v___jp_7029_:
{
if (v_clsEnabled_6992_ == 0)
{
if (v___y_7030_ == 0)
{
lean_object* v___x_7031_; lean_object* v_traceState_7032_; lean_object* v_env_7033_; lean_object* v_nextMacroScope_7034_; lean_object* v_ngen_7035_; lean_object* v_auxDeclNGen_7036_; lean_object* v_cache_7037_; lean_object* v_messages_7038_; lean_object* v_infoState_7039_; lean_object* v_snapshotTasks_7040_; lean_object* v___x_7042_; uint8_t v_isShared_7043_; uint8_t v_isSharedCheck_7059_; 
lean_dec(v_snd_7010_);
lean_dec(v_fst_7009_);
lean_dec_ref(v_msg_6994_);
lean_dec_ref(v_tag_6990_);
lean_dec(v_cls_6988_);
v___x_7031_ = lean_st_ref_take(v___y_6999_);
v_traceState_7032_ = lean_ctor_get(v___x_7031_, 4);
v_env_7033_ = lean_ctor_get(v___x_7031_, 0);
v_nextMacroScope_7034_ = lean_ctor_get(v___x_7031_, 1);
v_ngen_7035_ = lean_ctor_get(v___x_7031_, 2);
v_auxDeclNGen_7036_ = lean_ctor_get(v___x_7031_, 3);
v_cache_7037_ = lean_ctor_get(v___x_7031_, 5);
v_messages_7038_ = lean_ctor_get(v___x_7031_, 6);
v_infoState_7039_ = lean_ctor_get(v___x_7031_, 7);
v_snapshotTasks_7040_ = lean_ctor_get(v___x_7031_, 8);
v_isSharedCheck_7059_ = !lean_is_exclusive(v___x_7031_);
if (v_isSharedCheck_7059_ == 0)
{
v___x_7042_ = v___x_7031_;
v_isShared_7043_ = v_isSharedCheck_7059_;
goto v_resetjp_7041_;
}
else
{
lean_inc(v_snapshotTasks_7040_);
lean_inc(v_infoState_7039_);
lean_inc(v_messages_7038_);
lean_inc(v_cache_7037_);
lean_inc(v_traceState_7032_);
lean_inc(v_auxDeclNGen_7036_);
lean_inc(v_ngen_7035_);
lean_inc(v_nextMacroScope_7034_);
lean_inc(v_env_7033_);
lean_dec(v___x_7031_);
v___x_7042_ = lean_box(0);
v_isShared_7043_ = v_isSharedCheck_7059_;
goto v_resetjp_7041_;
}
v_resetjp_7041_:
{
uint64_t v_tid_7044_; lean_object* v_traces_7045_; lean_object* v___x_7047_; uint8_t v_isShared_7048_; uint8_t v_isSharedCheck_7058_; 
v_tid_7044_ = lean_ctor_get_uint64(v_traceState_7032_, sizeof(void*)*1);
v_traces_7045_ = lean_ctor_get(v_traceState_7032_, 0);
v_isSharedCheck_7058_ = !lean_is_exclusive(v_traceState_7032_);
if (v_isSharedCheck_7058_ == 0)
{
v___x_7047_ = v_traceState_7032_;
v_isShared_7048_ = v_isSharedCheck_7058_;
goto v_resetjp_7046_;
}
else
{
lean_inc(v_traces_7045_);
lean_dec(v_traceState_7032_);
v___x_7047_ = lean_box(0);
v_isShared_7048_ = v_isSharedCheck_7058_;
goto v_resetjp_7046_;
}
v_resetjp_7046_:
{
lean_object* v___x_7049_; lean_object* v___x_7051_; 
v___x_7049_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6993_, v_traces_7045_);
lean_dec_ref(v_traces_7045_);
if (v_isShared_7048_ == 0)
{
lean_ctor_set(v___x_7047_, 0, v___x_7049_);
v___x_7051_ = v___x_7047_;
goto v_reusejp_7050_;
}
else
{
lean_object* v_reuseFailAlloc_7057_; 
v_reuseFailAlloc_7057_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_7057_, 0, v___x_7049_);
lean_ctor_set_uint64(v_reuseFailAlloc_7057_, sizeof(void*)*1, v_tid_7044_);
v___x_7051_ = v_reuseFailAlloc_7057_;
goto v_reusejp_7050_;
}
v_reusejp_7050_:
{
lean_object* v___x_7053_; 
if (v_isShared_7043_ == 0)
{
lean_ctor_set(v___x_7042_, 4, v___x_7051_);
v___x_7053_ = v___x_7042_;
goto v_reusejp_7052_;
}
else
{
lean_object* v_reuseFailAlloc_7056_; 
v_reuseFailAlloc_7056_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_7056_, 0, v_env_7033_);
lean_ctor_set(v_reuseFailAlloc_7056_, 1, v_nextMacroScope_7034_);
lean_ctor_set(v_reuseFailAlloc_7056_, 2, v_ngen_7035_);
lean_ctor_set(v_reuseFailAlloc_7056_, 3, v_auxDeclNGen_7036_);
lean_ctor_set(v_reuseFailAlloc_7056_, 4, v___x_7051_);
lean_ctor_set(v_reuseFailAlloc_7056_, 5, v_cache_7037_);
lean_ctor_set(v_reuseFailAlloc_7056_, 6, v_messages_7038_);
lean_ctor_set(v_reuseFailAlloc_7056_, 7, v_infoState_7039_);
lean_ctor_set(v_reuseFailAlloc_7056_, 8, v_snapshotTasks_7040_);
v___x_7053_ = v_reuseFailAlloc_7056_;
goto v_reusejp_7052_;
}
v_reusejp_7052_:
{
lean_object* v___x_7054_; lean_object* v___x_7055_; 
v___x_7054_ = lean_st_ref_put(v___y_6999_, v___x_7053_);
v___x_7055_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_7001_);
return v___x_7055_;
}
}
}
}
}
else
{
goto v___jp_7024_;
}
}
else
{
goto v___jp_7024_;
}
}
v___jp_7060_:
{
double v___x_7062_; double v___x_7063_; double v___x_7064_; uint8_t v___x_7065_; 
v___x_7062_ = lean_unbox_float(v_snd_7010_);
v___x_7063_ = lean_unbox_float(v_fst_7009_);
v___x_7064_ = lean_float_sub(v___x_7062_, v___x_7063_);
v___x_7065_ = lean_float_decLt(v___y_7061_, v___x_7064_);
v___y_7030_ = v___x_7065_;
goto v___jp_7029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___boxed(lean_object* v_cls_7076_, lean_object* v_collapsed_7077_, lean_object* v_tag_7078_, lean_object* v_opts_7079_, lean_object* v_clsEnabled_7080_, lean_object* v_oldTraces_7081_, lean_object* v_msg_7082_, lean_object* v_resStartStop_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_){
_start:
{
uint8_t v_collapsed_boxed_7089_; uint8_t v_clsEnabled_boxed_7090_; lean_object* v_res_7091_; 
v_collapsed_boxed_7089_ = lean_unbox(v_collapsed_7077_);
v_clsEnabled_boxed_7090_ = lean_unbox(v_clsEnabled_7080_);
v_res_7091_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v_cls_7076_, v_collapsed_boxed_7089_, v_tag_7078_, v_opts_7079_, v_clsEnabled_boxed_7090_, v_oldTraces_7081_, v_msg_7082_, v_resStartStop_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_);
lean_dec(v___y_7087_);
lean_dec_ref(v___y_7086_);
lean_dec(v___y_7085_);
lean_dec_ref(v___y_7084_);
lean_dec_ref(v_opts_7079_);
return v_res_7091_;
}
}
static double _init_l_Lean_mkNoConfusion___closed__0(void){
_start:
{
lean_object* v___x_7092_; double v___x_7093_; 
v___x_7092_ = lean_unsigned_to_nat(1000000000u);
v___x_7093_ = lean_float_of_nat(v___x_7092_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion(lean_object* v_declName_7094_, lean_object* v_a_7095_, lean_object* v_a_7096_, lean_object* v_a_7097_, lean_object* v_a_7098_){
_start:
{
lean_object* v_toCold_7100_; lean_object* v_options_7101_; uint8_t v_hasTrace_7102_; 
v_toCold_7100_ = lean_ctor_get(v_a_7097_, 0);
v_options_7101_ = lean_ctor_get(v_toCold_7100_, 2);
v_hasTrace_7102_ = lean_ctor_get_uint8(v_options_7101_, sizeof(void*)*1);
if (v_hasTrace_7102_ == 0)
{
lean_object* v___x_7103_; 
lean_inc(v_declName_7094_);
v___x_7103_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
if (lean_obj_tag(v___x_7103_) == 0)
{
lean_object* v_a_7104_; uint8_t v___x_7105_; 
v_a_7104_ = lean_ctor_get(v___x_7103_, 0);
lean_inc(v_a_7104_);
lean_dec_ref_known(v___x_7103_, 1);
v___x_7105_ = lean_unbox(v_a_7104_);
lean_dec(v_a_7104_);
if (v___x_7105_ == 0)
{
lean_object* v___x_7106_; 
v___x_7106_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7106_;
}
else
{
lean_object* v___x_7107_; 
v___x_7107_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7107_;
}
}
else
{
lean_object* v_a_7108_; lean_object* v___x_7110_; uint8_t v_isShared_7111_; uint8_t v_isSharedCheck_7115_; 
lean_dec(v_declName_7094_);
v_a_7108_ = lean_ctor_get(v___x_7103_, 0);
v_isSharedCheck_7115_ = !lean_is_exclusive(v___x_7103_);
if (v_isSharedCheck_7115_ == 0)
{
v___x_7110_ = v___x_7103_;
v_isShared_7111_ = v_isSharedCheck_7115_;
goto v_resetjp_7109_;
}
else
{
lean_inc(v_a_7108_);
lean_dec(v___x_7103_);
v___x_7110_ = lean_box(0);
v_isShared_7111_ = v_isSharedCheck_7115_;
goto v_resetjp_7109_;
}
v_resetjp_7109_:
{
lean_object* v___x_7113_; 
if (v_isShared_7111_ == 0)
{
v___x_7113_ = v___x_7110_;
goto v_reusejp_7112_;
}
else
{
lean_object* v_reuseFailAlloc_7114_; 
v_reuseFailAlloc_7114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_a_7108_);
v___x_7113_ = v_reuseFailAlloc_7114_;
goto v_reusejp_7112_;
}
v_reusejp_7112_:
{
return v___x_7113_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_7116_; lean_object* v___f_7117_; lean_object* v___x_7118_; lean_object* v___x_7119_; lean_object* v___x_7120_; uint8_t v___x_7121_; lean_object* v___y_7123_; lean_object* v___y_7124_; lean_object* v_a_7125_; lean_object* v___y_7138_; lean_object* v___y_7139_; lean_object* v_a_7140_; lean_object* v___y_7143_; lean_object* v___y_7144_; lean_object* v___y_7145_; lean_object* v___y_7156_; lean_object* v___y_7157_; lean_object* v_a_7158_; lean_object* v___y_7168_; lean_object* v___y_7169_; lean_object* v_a_7170_; lean_object* v___y_7173_; lean_object* v___y_7174_; lean_object* v___y_7175_; 
v_inheritedTraceOptions_7116_ = lean_ctor_get(v_toCold_7100_, 11);
lean_inc(v_declName_7094_);
v___f_7117_ = lean_alloc_closure((void*)(l_Lean_mkNoConfusion___lam__0___boxed), 7, 1);
lean_closure_set(v___f_7117_, 0, v_declName_7094_);
v___x_7118_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_7120_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2);
v___x_7121_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7116_, v_options_7101_, v___x_7120_);
if (v___x_7121_ == 0)
{
lean_object* v___x_7204_; uint8_t v___x_7205_; 
v___x_7204_ = l_Lean_trace_profiler;
v___x_7205_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7101_, v___x_7204_);
if (v___x_7205_ == 0)
{
lean_object* v___x_7206_; 
lean_dec_ref(v___f_7117_);
lean_inc(v_declName_7094_);
v___x_7206_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
if (lean_obj_tag(v___x_7206_) == 0)
{
lean_object* v_a_7207_; uint8_t v___x_7208_; 
v_a_7207_ = lean_ctor_get(v___x_7206_, 0);
lean_inc(v_a_7207_);
lean_dec_ref_known(v___x_7206_, 1);
v___x_7208_ = lean_unbox(v_a_7207_);
lean_dec(v_a_7207_);
if (v___x_7208_ == 0)
{
lean_object* v___x_7209_; 
v___x_7209_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7209_;
}
else
{
lean_object* v___x_7210_; 
v___x_7210_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7210_;
}
}
else
{
lean_object* v_a_7211_; lean_object* v___x_7213_; uint8_t v_isShared_7214_; uint8_t v_isSharedCheck_7218_; 
lean_dec(v_declName_7094_);
v_a_7211_ = lean_ctor_get(v___x_7206_, 0);
v_isSharedCheck_7218_ = !lean_is_exclusive(v___x_7206_);
if (v_isSharedCheck_7218_ == 0)
{
v___x_7213_ = v___x_7206_;
v_isShared_7214_ = v_isSharedCheck_7218_;
goto v_resetjp_7212_;
}
else
{
lean_inc(v_a_7211_);
lean_dec(v___x_7206_);
v___x_7213_ = lean_box(0);
v_isShared_7214_ = v_isSharedCheck_7218_;
goto v_resetjp_7212_;
}
v_resetjp_7212_:
{
lean_object* v___x_7216_; 
if (v_isShared_7214_ == 0)
{
v___x_7216_ = v___x_7213_;
goto v_reusejp_7215_;
}
else
{
lean_object* v_reuseFailAlloc_7217_; 
v_reuseFailAlloc_7217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7217_, 0, v_a_7211_);
v___x_7216_ = v_reuseFailAlloc_7217_;
goto v_reusejp_7215_;
}
v_reusejp_7215_:
{
return v___x_7216_;
}
}
}
}
else
{
goto v___jp_7185_;
}
}
else
{
goto v___jp_7185_;
}
v___jp_7122_:
{
lean_object* v___x_7126_; double v___x_7127_; double v___x_7128_; double v___x_7129_; double v___x_7130_; double v___x_7131_; lean_object* v___x_7132_; lean_object* v___x_7133_; lean_object* v___x_7134_; lean_object* v___x_7135_; lean_object* v___x_7136_; 
v___x_7126_ = lean_io_mono_nanos_now();
v___x_7127_ = lean_float_of_nat(v___y_7123_);
v___x_7128_ = lean_float_once(&l_Lean_mkNoConfusion___closed__0, &l_Lean_mkNoConfusion___closed__0_once, _init_l_Lean_mkNoConfusion___closed__0);
v___x_7129_ = lean_float_div(v___x_7127_, v___x_7128_);
v___x_7130_ = lean_float_of_nat(v___x_7126_);
v___x_7131_ = lean_float_div(v___x_7130_, v___x_7128_);
v___x_7132_ = lean_box_float(v___x_7129_);
v___x_7133_ = lean_box_float(v___x_7131_);
v___x_7134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7134_, 0, v___x_7132_);
lean_ctor_set(v___x_7134_, 1, v___x_7133_);
v___x_7135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7135_, 0, v_a_7125_);
lean_ctor_set(v___x_7135_, 1, v___x_7134_);
v___x_7136_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7118_, v_hasTrace_7102_, v___x_7119_, v_options_7101_, v___x_7121_, v___y_7124_, v___f_7117_, v___x_7135_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7136_;
}
v___jp_7137_:
{
lean_object* v___x_7141_; 
v___x_7141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7141_, 0, v_a_7140_);
v___y_7123_ = v___y_7138_;
v___y_7124_ = v___y_7139_;
v_a_7125_ = v___x_7141_;
goto v___jp_7122_;
}
v___jp_7142_:
{
if (lean_obj_tag(v___y_7145_) == 0)
{
lean_object* v_a_7146_; lean_object* v___x_7148_; uint8_t v_isShared_7149_; uint8_t v_isSharedCheck_7153_; 
v_a_7146_ = lean_ctor_get(v___y_7145_, 0);
v_isSharedCheck_7153_ = !lean_is_exclusive(v___y_7145_);
if (v_isSharedCheck_7153_ == 0)
{
v___x_7148_ = v___y_7145_;
v_isShared_7149_ = v_isSharedCheck_7153_;
goto v_resetjp_7147_;
}
else
{
lean_inc(v_a_7146_);
lean_dec(v___y_7145_);
v___x_7148_ = lean_box(0);
v_isShared_7149_ = v_isSharedCheck_7153_;
goto v_resetjp_7147_;
}
v_resetjp_7147_:
{
lean_object* v___x_7151_; 
if (v_isShared_7149_ == 0)
{
lean_ctor_set_tag(v___x_7148_, 1);
v___x_7151_ = v___x_7148_;
goto v_reusejp_7150_;
}
else
{
lean_object* v_reuseFailAlloc_7152_; 
v_reuseFailAlloc_7152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7152_, 0, v_a_7146_);
v___x_7151_ = v_reuseFailAlloc_7152_;
goto v_reusejp_7150_;
}
v_reusejp_7150_:
{
v___y_7123_ = v___y_7143_;
v___y_7124_ = v___y_7144_;
v_a_7125_ = v___x_7151_;
goto v___jp_7122_;
}
}
}
else
{
lean_object* v_a_7154_; 
v_a_7154_ = lean_ctor_get(v___y_7145_, 0);
lean_inc(v_a_7154_);
lean_dec_ref_known(v___y_7145_, 1);
v___y_7138_ = v___y_7143_;
v___y_7139_ = v___y_7144_;
v_a_7140_ = v_a_7154_;
goto v___jp_7137_;
}
}
v___jp_7155_:
{
lean_object* v___x_7159_; double v___x_7160_; double v___x_7161_; lean_object* v___x_7162_; lean_object* v___x_7163_; lean_object* v___x_7164_; lean_object* v___x_7165_; lean_object* v___x_7166_; 
v___x_7159_ = lean_io_get_num_heartbeats();
v___x_7160_ = lean_float_of_nat(v___y_7157_);
v___x_7161_ = lean_float_of_nat(v___x_7159_);
v___x_7162_ = lean_box_float(v___x_7160_);
v___x_7163_ = lean_box_float(v___x_7161_);
v___x_7164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7164_, 0, v___x_7162_);
lean_ctor_set(v___x_7164_, 1, v___x_7163_);
v___x_7165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7165_, 0, v_a_7158_);
lean_ctor_set(v___x_7165_, 1, v___x_7164_);
v___x_7166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7118_, v_hasTrace_7102_, v___x_7119_, v_options_7101_, v___x_7121_, v___y_7156_, v___f_7117_, v___x_7165_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
return v___x_7166_;
}
v___jp_7167_:
{
lean_object* v___x_7171_; 
v___x_7171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7171_, 0, v_a_7170_);
v___y_7156_ = v___y_7168_;
v___y_7157_ = v___y_7169_;
v_a_7158_ = v___x_7171_;
goto v___jp_7155_;
}
v___jp_7172_:
{
if (lean_obj_tag(v___y_7175_) == 0)
{
lean_object* v_a_7176_; lean_object* v___x_7178_; uint8_t v_isShared_7179_; uint8_t v_isSharedCheck_7183_; 
v_a_7176_ = lean_ctor_get(v___y_7175_, 0);
v_isSharedCheck_7183_ = !lean_is_exclusive(v___y_7175_);
if (v_isSharedCheck_7183_ == 0)
{
v___x_7178_ = v___y_7175_;
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
else
{
lean_inc(v_a_7176_);
lean_dec(v___y_7175_);
v___x_7178_ = lean_box(0);
v_isShared_7179_ = v_isSharedCheck_7183_;
goto v_resetjp_7177_;
}
v_resetjp_7177_:
{
lean_object* v___x_7181_; 
if (v_isShared_7179_ == 0)
{
lean_ctor_set_tag(v___x_7178_, 1);
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
v___y_7156_ = v___y_7173_;
v___y_7157_ = v___y_7174_;
v_a_7158_ = v___x_7181_;
goto v___jp_7155_;
}
}
}
else
{
lean_object* v_a_7184_; 
v_a_7184_ = lean_ctor_get(v___y_7175_, 0);
lean_inc(v_a_7184_);
lean_dec_ref_known(v___y_7175_, 1);
v___y_7168_ = v___y_7173_;
v___y_7169_ = v___y_7174_;
v_a_7170_ = v_a_7184_;
goto v___jp_7167_;
}
}
v___jp_7185_:
{
lean_object* v___x_7186_; lean_object* v_a_7187_; lean_object* v___x_7188_; uint8_t v___x_7189_; 
v___x_7186_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v_a_7098_);
v_a_7187_ = lean_ctor_get(v___x_7186_, 0);
lean_inc(v_a_7187_);
lean_dec_ref(v___x_7186_);
v___x_7188_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7189_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7101_, v___x_7188_);
if (v___x_7189_ == 0)
{
lean_object* v___x_7190_; lean_object* v___x_7191_; 
v___x_7190_ = lean_io_mono_nanos_now();
lean_inc(v_declName_7094_);
v___x_7191_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
if (lean_obj_tag(v___x_7191_) == 0)
{
lean_object* v_a_7192_; uint8_t v___x_7193_; 
v_a_7192_ = lean_ctor_get(v___x_7191_, 0);
lean_inc(v_a_7192_);
lean_dec_ref_known(v___x_7191_, 1);
v___x_7193_ = lean_unbox(v_a_7192_);
lean_dec(v_a_7192_);
if (v___x_7193_ == 0)
{
lean_object* v___x_7194_; 
v___x_7194_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
v___y_7143_ = v___x_7190_;
v___y_7144_ = v_a_7187_;
v___y_7145_ = v___x_7194_;
goto v___jp_7142_;
}
else
{
lean_object* v___x_7195_; 
v___x_7195_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
v___y_7143_ = v___x_7190_;
v___y_7144_ = v_a_7187_;
v___y_7145_ = v___x_7195_;
goto v___jp_7142_;
}
}
else
{
lean_object* v_a_7196_; 
lean_dec(v_declName_7094_);
v_a_7196_ = lean_ctor_get(v___x_7191_, 0);
lean_inc(v_a_7196_);
lean_dec_ref_known(v___x_7191_, 1);
v___y_7138_ = v___x_7190_;
v___y_7139_ = v_a_7187_;
v_a_7140_ = v_a_7196_;
goto v___jp_7137_;
}
}
else
{
lean_object* v___x_7197_; lean_object* v___x_7198_; 
v___x_7197_ = lean_io_get_num_heartbeats();
lean_inc(v_declName_7094_);
v___x_7198_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
if (lean_obj_tag(v___x_7198_) == 0)
{
lean_object* v_a_7199_; uint8_t v___x_7200_; 
v_a_7199_ = lean_ctor_get(v___x_7198_, 0);
lean_inc(v_a_7199_);
lean_dec_ref_known(v___x_7198_, 1);
v___x_7200_ = lean_unbox(v_a_7199_);
lean_dec(v_a_7199_);
if (v___x_7200_ == 0)
{
lean_object* v___x_7201_; 
v___x_7201_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
v___y_7173_ = v_a_7187_;
v___y_7174_ = v___x_7197_;
v___y_7175_ = v___x_7201_;
goto v___jp_7172_;
}
else
{
lean_object* v___x_7202_; 
v___x_7202_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7094_, v_a_7095_, v_a_7096_, v_a_7097_, v_a_7098_);
v___y_7173_ = v_a_7187_;
v___y_7174_ = v___x_7197_;
v___y_7175_ = v___x_7202_;
goto v___jp_7172_;
}
}
else
{
lean_object* v_a_7203_; 
lean_dec(v_declName_7094_);
v_a_7203_ = lean_ctor_get(v___x_7198_, 0);
lean_inc(v_a_7203_);
lean_dec_ref_known(v___x_7198_, 1);
v___y_7168_ = v_a_7187_;
v___y_7169_ = v___x_7197_;
v_a_7170_ = v_a_7203_;
goto v___jp_7167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___boxed(lean_object* v_declName_7219_, lean_object* v_a_7220_, lean_object* v_a_7221_, lean_object* v_a_7222_, lean_object* v_a_7223_, lean_object* v_a_7224_){
_start:
{
lean_object* v_res_7225_; 
v_res_7225_ = l_Lean_mkNoConfusion(v_declName_7219_, v_a_7220_, v_a_7221_, v_a_7222_, v_a_7223_);
lean_dec(v_a_7223_);
lean_dec_ref(v_a_7222_);
lean_dec(v_a_7221_);
lean_dec_ref(v_a_7220_);
return v_res_7225_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(lean_object* v_00_u03b1_7226_, lean_object* v_x_7227_, lean_object* v___y_7228_, lean_object* v___y_7229_, lean_object* v___y_7230_, lean_object* v___y_7231_){
_start:
{
lean_object* v___x_7233_; 
v___x_7233_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_7227_);
return v___x_7233_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___boxed(lean_object* v_00_u03b1_7234_, lean_object* v_x_7235_, lean_object* v___y_7236_, lean_object* v___y_7237_, lean_object* v___y_7238_, lean_object* v___y_7239_, lean_object* v___y_7240_){
_start:
{
lean_object* v_res_7241_; 
v_res_7241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(v_00_u03b1_7234_, v_x_7235_, v___y_7236_, v___y_7237_, v___y_7238_, v___y_7239_);
lean_dec(v___y_7239_);
lean_dec_ref(v___y_7238_);
lean_dec(v___y_7237_);
lean_dec_ref(v___y_7236_);
return v_res_7241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7277_; uint8_t v___x_7278_; lean_object* v___x_7279_; lean_object* v___x_7280_; 
v___x_7277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7278_ = 0;
v___x_7279_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_));
v___x_7280_ = l_Lean_registerTraceClass(v___x_7277_, v___x_7278_, v___x_7279_);
return v___x_7280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2____boxed(lean_object* v_a_7281_){
_start:
{
lean_object* v_res_7282_; 
v_res_7282_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_();
return v_res_7282_;
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
