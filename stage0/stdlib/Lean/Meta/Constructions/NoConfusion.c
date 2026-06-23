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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_mkCtorIdxName(lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_markNoConfusion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___boxed(lean_object**);
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
static lean_once_cell_t l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4;
static lean_once_cell_t l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(34, 153, 146, 175, 179, 220, 230, 134)}};
static const lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__7_value;
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
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
size_t v_sz_boxed_342_; size_t v___x_4697__boxed_343_; lean_object* v_res_344_; 
v_sz_boxed_342_ = lean_unbox_usize(v_sz_330_);
lean_dec(v_sz_330_);
v___x_4697__boxed_343_ = lean_unbox_usize(v___x_331_);
lean_dec(v___x_331_);
v_res_344_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg___lam__0(v___x_329_, v_sz_boxed_342_, v___x_4697__boxed_343_, v___x_332_, v_xs1_333_, v_fields1_334_, v_xs2_335_, v_fields2_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
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
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_3620__overap_520_; lean_object* v___x_521_; 
v___x_518_ = lean_box(0);
v___x_519_ = l_instInhabitedOfMonad___redArg(v___x_517_, v___x_518_);
v___x_3620__overap_520_ = lean_panic_fn_borrowed(v___x_519_, v_msg_463_);
lean_dec(v___x_519_);
lean_inc(v___y_467_);
lean_inc_ref(v___y_466_);
lean_inc(v___y_465_);
lean_inc_ref(v___y_464_);
v___x_521_ = lean_apply_5(v___x_3620__overap_520_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, lean_box(0));
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
lean_object* v___f_1254_; lean_object* v___x_13924__overap_1255_; lean_object* v___x_1256_; 
v___f_1254_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_13924__overap_1255_ = lean_panic_fn_borrowed(v___f_1254_, v_msg_1248_);
lean_inc(v___y_1252_);
lean_inc_ref(v___y_1251_);
lean_inc(v___y_1250_);
lean_inc_ref(v___y_1249_);
v___x_1256_ = lean_apply_5(v___x_13924__overap_1255_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, lean_box(0));
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
uint8_t v___x_16895__boxed_1285_; lean_object* v_res_1286_; 
v___x_16895__boxed_1285_ = lean_unbox(v___x_1277_);
v_res_1286_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0(v___x_1276_, v___x_16895__boxed_1285_, v_ys_1278_, v_x_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec_ref(v_x_1279_);
lean_dec_ref(v_ys_1278_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(lean_object* v_i_1287_, lean_object* v_j_1288_, lean_object* v_P_1289_, uint8_t v_isZero_1290_, uint8_t v___x_1291_, lean_object* v___x_1292_, lean_object* v_xs1_1293_, lean_object* v_zs1_1294_, lean_object* v_xs2_1295_, lean_object* v_zs2_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v___x_1303_; 
v___x_1303_ = lean_nat_dec_eq(v_i_1287_, v_j_1288_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_xs1_1293_);
lean_dec(v___x_1292_);
v___x_1304_ = 1;
v___x_1305_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1296_, v_P_1289_, v_isZero_1290_, v___x_1291_, v_isZero_1290_, v___x_1291_, v___x_1304_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
lean_inc_ref(v_P_1289_);
v___x_1306_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1292_, v_P_1289_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Array_append___redArg(v_xs1_1293_, v_zs1_1294_);
v___x_1309_ = l_Array_append___redArg(v___x_1308_, v_xs2_1295_);
v___x_1310_ = l_Array_append___redArg(v___x_1309_, v_zs2_1296_);
v___x_1311_ = l_Lean_Expr_beta(v_a_1307_, v___x_1310_);
v___x_1312_ = l_Lean_mkArrow(v___x_1311_, v_P_1289_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = 1;
v___x_1315_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1296_, v_a_1313_, v_isZero_1290_, v___x_1291_, v_isZero_1290_, v___x_1291_, v___x_1314_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
return v___x_1315_;
}
else
{
return v___x_1312_;
}
}
else
{
lean_dec_ref(v_xs1_1293_);
lean_dec_ref(v_P_1289_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed(lean_object* v_i_1316_, lean_object* v_j_1317_, lean_object* v_P_1318_, lean_object* v_isZero_1319_, lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v_xs1_1322_, lean_object* v_zs1_1323_, lean_object* v_xs2_1324_, lean_object* v_zs2_1325_, lean_object* v_x_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v_isZero_boxed_1332_; uint8_t v___x_16924__boxed_1333_; lean_object* v_res_1334_; 
v_isZero_boxed_1332_ = lean_unbox(v_isZero_1319_);
v___x_16924__boxed_1333_ = lean_unbox(v___x_1320_);
v_res_1334_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0(v_i_1316_, v_j_1317_, v_P_1318_, v_isZero_boxed_1332_, v___x_16924__boxed_1333_, v___x_1321_, v_xs1_1322_, v_zs1_1323_, v_xs2_1324_, v_zs2_1325_, v_x_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v_x_1326_);
lean_dec_ref(v_zs2_1325_);
lean_dec_ref(v_xs2_1324_);
lean_dec_ref(v_zs1_1323_);
lean_dec(v_j_1317_);
lean_dec(v_i_1316_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(lean_object* v_i_1335_, lean_object* v_P_1336_, lean_object* v___x_1337_, lean_object* v_xs1_1338_, lean_object* v_zs1_1339_, lean_object* v_xs2_1340_, lean_object* v_as_1341_, lean_object* v_i_1342_, lean_object* v_j_1343_, lean_object* v_bs_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v_zero_1350_; uint8_t v_isZero_1351_; 
v_zero_1350_ = lean_unsigned_to_nat(0u);
v_isZero_1351_ = lean_nat_dec_eq(v_i_1342_, v_zero_1350_);
if (v_isZero_1351_ == 1)
{
lean_object* v___x_1352_; 
lean_dec(v_j_1343_);
lean_dec(v_i_1342_);
lean_dec_ref(v_xs2_1340_);
lean_dec_ref(v_zs1_1339_);
lean_dec_ref(v_xs1_1338_);
lean_dec(v___x_1337_);
lean_dec_ref(v_P_1336_);
lean_dec(v_i_1335_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_bs_1344_);
return v___x_1352_;
}
else
{
uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1353_ = 1;
v___x_1354_ = lean_box(v_isZero_1351_);
v___x_1355_ = lean_box(v___x_1353_);
lean_inc_ref(v_xs2_1340_);
lean_inc_ref(v_zs1_1339_);
lean_inc_ref(v_xs1_1338_);
lean_inc(v___x_1337_);
lean_inc_ref(v_P_1336_);
lean_inc(v_j_1343_);
lean_inc(v_i_1335_);
v___f_1356_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1356_, 0, v_i_1335_);
lean_closure_set(v___f_1356_, 1, v_j_1343_);
lean_closure_set(v___f_1356_, 2, v_P_1336_);
lean_closure_set(v___f_1356_, 3, v___x_1354_);
lean_closure_set(v___f_1356_, 4, v___x_1355_);
lean_closure_set(v___f_1356_, 5, v___x_1337_);
lean_closure_set(v___f_1356_, 6, v_xs1_1338_);
lean_closure_set(v___f_1356_, 7, v_zs1_1339_);
lean_closure_set(v___f_1356_, 8, v_xs2_1340_);
v___x_1357_ = lean_array_fget_borrowed(v_as_1341_, v_j_1343_);
lean_inc(v___x_1357_);
v___x_1358_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1357_, v___f_1356_, v_isZero_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_one_1360_; lean_object* v_n_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v_one_1360_ = lean_unsigned_to_nat(1u);
v_n_1361_ = lean_nat_sub(v_i_1342_, v_one_1360_);
lean_dec(v_i_1342_);
v___x_1362_ = lean_nat_add(v_j_1343_, v_one_1360_);
lean_dec(v_j_1343_);
v___x_1363_ = lean_array_push(v_bs_1344_, v_a_1359_);
v_i_1342_ = v_n_1361_;
v_j_1343_ = v___x_1362_;
v_bs_1344_ = v___x_1363_;
goto _start;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_bs_1344_);
lean_dec(v_j_1343_);
lean_dec(v_i_1342_);
lean_dec_ref(v_xs2_1340_);
lean_dec_ref(v_zs1_1339_);
lean_dec_ref(v_xs1_1338_);
lean_dec(v___x_1337_);
lean_dec_ref(v_P_1336_);
lean_dec(v_i_1335_);
v_a_1365_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1358_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1358_);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg___boxed(lean_object* v_i_1373_, lean_object* v_P_1374_, lean_object* v___x_1375_, lean_object* v_xs1_1376_, lean_object* v_zs1_1377_, lean_object* v_xs2_1378_, lean_object* v_as_1379_, lean_object* v_i_1380_, lean_object* v_j_1381_, lean_object* v_bs_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_1373_, v_P_1374_, v___x_1375_, v_xs1_1376_, v_zs1_1377_, v_xs2_1378_, v_as_1379_, v_i_1380_, v_j_1381_, v_bs_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec_ref(v_as_1379_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(lean_object* v___x_1389_, lean_object* v_P_1390_, lean_object* v_xs1_1391_, lean_object* v_zs1_1392_, lean_object* v_xs2_1393_, uint8_t v_isZero_1394_, uint8_t v___x_1395_, lean_object* v_zs2_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
lean_inc_ref(v_P_1390_);
v___x_1403_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v___x_1389_, v_P_1390_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1405_ = l_Array_append___redArg(v_xs1_1391_, v_zs1_1392_);
v___x_1406_ = l_Array_append___redArg(v___x_1405_, v_xs2_1393_);
v___x_1407_ = l_Array_append___redArg(v___x_1406_, v_zs2_1396_);
v___x_1408_ = l_Lean_Expr_beta(v_a_1404_, v___x_1407_);
v___x_1409_ = l_Lean_mkArrow(v___x_1408_, v_P_1390_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; uint8_t v___x_1411_; lean_object* v___x_1412_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
v___x_1411_ = 1;
v___x_1412_ = l_Lean_Meta_mkLambdaFVars(v_zs2_1396_, v_a_1410_, v_isZero_1394_, v___x_1395_, v_isZero_1394_, v___x_1395_, v___x_1411_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1412_;
}
else
{
return v___x_1409_;
}
}
else
{
lean_dec_ref(v_xs1_1391_);
lean_dec_ref(v_P_1390_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed(lean_object* v___x_1413_, lean_object* v_P_1414_, lean_object* v_xs1_1415_, lean_object* v_zs1_1416_, lean_object* v_xs2_1417_, lean_object* v_isZero_1418_, lean_object* v___x_1419_, lean_object* v_zs2_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
uint8_t v_isZero_boxed_1427_; uint8_t v___x_17035__boxed_1428_; lean_object* v_res_1429_; 
v_isZero_boxed_1427_ = lean_unbox(v_isZero_1418_);
v___x_17035__boxed_1428_ = lean_unbox(v___x_1419_);
v_res_1429_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1(v___x_1413_, v_P_1414_, v_xs1_1415_, v_zs1_1416_, v_xs2_1417_, v_isZero_boxed_1427_, v___x_17035__boxed_1428_, v_zs2_1420_, v_x_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_x_1421_);
lean_dec_ref(v_zs2_1420_);
lean_dec_ref(v_xs2_1417_);
lean_dec_ref(v_zs1_1416_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(lean_object* v_val_1430_, lean_object* v_j_1431_, lean_object* v_indName_1432_, lean_object* v___x_1433_, lean_object* v_xs2_1434_, lean_object* v___x_1435_, lean_object* v_ysx2_1436_, lean_object* v_P_1437_, lean_object* v_xs1_1438_, lean_object* v_zs1_1439_, uint8_t v_isZero_1440_, uint8_t v___x_1441_, lean_object* v_h_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_ctors_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_ctors_1448_ = lean_ctor_get(v_val_1430_, 4);
v___x_1449_ = lean_box(0);
v___x_1450_ = l_List_get_x21Internal___redArg(v___x_1449_, v_ctors_1448_, v_j_1431_);
lean_inc(v___x_1450_);
v___x_1451_ = l_Lean_mkConstructorElimName(v_indName_1432_, v___x_1450_);
v___x_1452_ = l_Lean_mkConst(v___x_1451_, v___x_1433_);
lean_inc_ref(v_xs2_1434_);
v___x_1453_ = l_Array_append___redArg(v_xs2_1434_, v___x_1435_);
v___x_1454_ = l_Array_append___redArg(v___x_1453_, v_ysx2_1436_);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_mk_empty_array_with_capacity(v___x_1455_);
v___x_1457_ = lean_array_push(v___x_1456_, v_h_1442_);
v___x_1458_ = l_Array_append___redArg(v___x_1454_, v___x_1457_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = l_Lean_mkAppN(v___x_1452_, v___x_1458_);
lean_dec_ref(v___x_1458_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc_ref(v___x_1459_);
v___x_1460_ = lean_infer_type(v___x_1459_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
v___x_1462_ = lean_whnf(v_a_1461_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___f_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = lean_box(v_isZero_1440_);
v___x_1465_ = lean_box(v___x_1441_);
v___f_1466_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1466_, 0, v___x_1450_);
lean_closure_set(v___f_1466_, 1, v_P_1437_);
lean_closure_set(v___f_1466_, 2, v_xs1_1438_);
lean_closure_set(v___f_1466_, 3, v_zs1_1439_);
lean_closure_set(v___f_1466_, 4, v_xs2_1434_);
lean_closure_set(v___f_1466_, 5, v___x_1464_);
lean_closure_set(v___f_1466_, 6, v___x_1465_);
v___x_1467_ = l_Lean_Expr_bindingDomain_x21(v_a_1463_);
lean_dec(v_a_1463_);
v___x_1468_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__3___redArg(v___x_1467_, v___f_1466_, v_isZero_1440_, v_isZero_1440_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = l_Lean_Expr_app___override(v___x_1459_, v_a_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1473_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
else
{
lean_dec_ref(v___x_1459_);
return v___x_1468_;
}
}
else
{
lean_dec_ref(v___x_1459_);
lean_dec(v___x_1450_);
lean_dec_ref(v_zs1_1439_);
lean_dec_ref(v_xs1_1438_);
lean_dec_ref(v_P_1437_);
lean_dec_ref(v_xs2_1434_);
return v___x_1462_;
}
}
else
{
lean_dec_ref(v___x_1459_);
lean_dec(v___x_1450_);
lean_dec_ref(v_zs1_1439_);
lean_dec_ref(v_xs1_1438_);
lean_dec_ref(v_P_1437_);
lean_dec_ref(v_xs2_1434_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v_val_1478_ = _args[0];
lean_object* v_j_1479_ = _args[1];
lean_object* v_indName_1480_ = _args[2];
lean_object* v___x_1481_ = _args[3];
lean_object* v_xs2_1482_ = _args[4];
lean_object* v___x_1483_ = _args[5];
lean_object* v_ysx2_1484_ = _args[6];
lean_object* v_P_1485_ = _args[7];
lean_object* v_xs1_1486_ = _args[8];
lean_object* v_zs1_1487_ = _args[9];
lean_object* v_isZero_1488_ = _args[10];
lean_object* v___x_1489_ = _args[11];
lean_object* v_h_1490_ = _args[12];
lean_object* v___y_1491_ = _args[13];
lean_object* v___y_1492_ = _args[14];
lean_object* v___y_1493_ = _args[15];
lean_object* v___y_1494_ = _args[16];
lean_object* v___y_1495_ = _args[17];
_start:
{
uint8_t v_isZero_boxed_1496_; uint8_t v___x_17083__boxed_1497_; lean_object* v_res_1498_; 
v_isZero_boxed_1496_ = lean_unbox(v_isZero_1488_);
v___x_17083__boxed_1497_ = lean_unbox(v___x_1489_);
v_res_1498_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2(v_val_1478_, v_j_1479_, v_indName_1480_, v___x_1481_, v_xs2_1482_, v___x_1483_, v_ysx2_1484_, v_P_1485_, v_xs1_1486_, v_zs1_1487_, v_isZero_boxed_1496_, v___x_17083__boxed_1497_, v_h_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec_ref(v_ysx2_1484_);
lean_dec_ref(v___x_1483_);
lean_dec_ref(v_val_1478_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(uint8_t v___y_1499_, lean_object* v_xs2_1500_, lean_object* v___x_1501_, lean_object* v_ysx2_1502_, lean_object* v___x_1503_, lean_object* v___x_1504_, lean_object* v_val_1505_, lean_object* v_j_1506_, lean_object* v_P_1507_, lean_object* v_xs1_1508_, uint8_t v_isZero_1509_, uint8_t v___x_1510_, lean_object* v_indName_1511_, lean_object* v___x_1512_, lean_object* v_tail_1513_, lean_object* v___x_1514_, lean_object* v___f_1515_, lean_object* v_zs1_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
if (v___y_1499_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref(v___f_1515_);
lean_dec_ref(v___x_1514_);
lean_dec(v_tail_1513_);
lean_dec(v___x_1512_);
lean_dec(v_indName_1511_);
lean_inc_ref(v_xs2_1500_);
v___x_1523_ = l_Array_append___redArg(v_xs2_1500_, v___x_1501_);
lean_dec_ref(v___x_1501_);
v___x_1524_ = l_Array_append___redArg(v___x_1523_, v_ysx2_1502_);
lean_dec_ref(v_ysx2_1502_);
v___x_1525_ = l_Lean_mkAppN(v___x_1503_, v___x_1524_);
lean_dec_ref(v___x_1524_);
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc_ref(v___x_1525_);
v___x_1526_ = lean_infer_type(v___x_1525_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = l_Lean_Meta_arrowDomainsN(v___x_1504_, v_a_1527_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v_ctors_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v_ctors_1530_ = lean_ctor_get(v_val_1505_, 4);
lean_inc(v_ctors_1530_);
lean_dec_ref(v_val_1505_);
v___x_1531_ = lean_box(0);
lean_inc(v_j_1506_);
v___x_1532_ = l_List_get_x21Internal___redArg(v___x_1531_, v_ctors_1530_, v_j_1506_);
lean_dec(v_ctors_1530_);
v___x_1533_ = lean_array_get_size(v_a_1529_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_mk_empty_array_with_capacity(v___x_1533_);
lean_inc_ref(v_zs1_1516_);
v___x_1536_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_j_1506_, v_P_1507_, v___x_1532_, v_xs1_1508_, v_zs1_1516_, v_xs2_1500_, v_a_1529_, v___x_1533_, v___x_1534_, v___x_1535_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v_a_1529_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v___x_1538_ = l_Lean_mkAppN(v___x_1525_, v_a_1537_);
lean_dec(v_a_1537_);
v___x_1539_ = 1;
v___x_1540_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1516_, v___x_1538_, v_isZero_1509_, v___x_1510_, v_isZero_1509_, v___x_1510_, v___x_1539_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v_zs1_1516_);
return v___x_1540_;
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v___x_1525_);
lean_dec_ref(v_zs1_1516_);
v_a_1541_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1536_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1536_);
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
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v___x_1525_);
lean_dec_ref(v_zs1_1516_);
lean_dec_ref(v_xs1_1508_);
lean_dec_ref(v_P_1507_);
lean_dec(v_j_1506_);
lean_dec_ref(v_val_1505_);
lean_dec_ref(v_xs2_1500_);
v_a_1549_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1528_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1528_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_dec_ref(v___x_1525_);
lean_dec_ref(v_zs1_1516_);
lean_dec_ref(v_xs1_1508_);
lean_dec_ref(v_P_1507_);
lean_dec(v_j_1506_);
lean_dec_ref(v_val_1505_);
lean_dec(v___x_1504_);
lean_dec_ref(v_xs2_1500_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v___x_1504_);
lean_dec_ref(v___x_1503_);
v___x_1557_ = lean_box(v_isZero_1509_);
v___x_1558_ = lean_box(v___x_1510_);
lean_inc_ref(v_zs1_1516_);
lean_inc_ref(v_ysx2_1502_);
lean_inc_ref(v_xs2_1500_);
lean_inc(v_indName_1511_);
lean_inc(v_j_1506_);
v___f_1559_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__2___boxed), 18, 12);
lean_closure_set(v___f_1559_, 0, v_val_1505_);
lean_closure_set(v___f_1559_, 1, v_j_1506_);
lean_closure_set(v___f_1559_, 2, v_indName_1511_);
lean_closure_set(v___f_1559_, 3, v___x_1512_);
lean_closure_set(v___f_1559_, 4, v_xs2_1500_);
lean_closure_set(v___f_1559_, 5, v___x_1501_);
lean_closure_set(v___f_1559_, 6, v_ysx2_1502_);
lean_closure_set(v___f_1559_, 7, v_P_1507_);
lean_closure_set(v___f_1559_, 8, v_xs1_1508_);
lean_closure_set(v___f_1559_, 9, v_zs1_1516_);
lean_closure_set(v___f_1559_, 10, v___x_1557_);
lean_closure_set(v___f_1559_, 11, v___x_1558_);
v___x_1560_ = l_mkCtorIdxName(v_indName_1511_);
v___x_1561_ = l_Lean_mkConst(v___x_1560_, v_tail_1513_);
v___x_1562_ = l_Array_append___redArg(v_xs2_1500_, v_ysx2_1502_);
lean_dec_ref(v_ysx2_1502_);
v___x_1563_ = l_Lean_mkAppN(v___x_1561_, v___x_1562_);
lean_dec_ref(v___x_1562_);
v___x_1564_ = l_Lean_mkRawNatLit(v_j_1506_);
v___x_1565_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq(v___x_1514_, v___x_1563_, v___x_1564_, v___f_1559_, v___f_1515_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = 1;
v___x_1568_ = l_Lean_Meta_mkLambdaFVars(v_zs1_1516_, v_a_1566_, v_isZero_1509_, v___x_1510_, v_isZero_1509_, v___x_1510_, v___x_1567_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v_zs1_1516_);
return v___x_1568_;
}
else
{
lean_dec_ref(v_zs1_1516_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___y_1569_ = _args[0];
lean_object* v_xs2_1570_ = _args[1];
lean_object* v___x_1571_ = _args[2];
lean_object* v_ysx2_1572_ = _args[3];
lean_object* v___x_1573_ = _args[4];
lean_object* v___x_1574_ = _args[5];
lean_object* v_val_1575_ = _args[6];
lean_object* v_j_1576_ = _args[7];
lean_object* v_P_1577_ = _args[8];
lean_object* v_xs1_1578_ = _args[9];
lean_object* v_isZero_1579_ = _args[10];
lean_object* v___x_1580_ = _args[11];
lean_object* v_indName_1581_ = _args[12];
lean_object* v___x_1582_ = _args[13];
lean_object* v_tail_1583_ = _args[14];
lean_object* v___x_1584_ = _args[15];
lean_object* v___f_1585_ = _args[16];
lean_object* v_zs1_1586_ = _args[17];
lean_object* v_x_1587_ = _args[18];
lean_object* v___y_1588_ = _args[19];
lean_object* v___y_1589_ = _args[20];
lean_object* v___y_1590_ = _args[21];
lean_object* v___y_1591_ = _args[22];
lean_object* v___y_1592_ = _args[23];
_start:
{
uint8_t v___y_17168__boxed_1593_; uint8_t v_isZero_boxed_1594_; uint8_t v___x_17173__boxed_1595_; lean_object* v_res_1596_; 
v___y_17168__boxed_1593_ = lean_unbox(v___y_1569_);
v_isZero_boxed_1594_ = lean_unbox(v_isZero_1579_);
v___x_17173__boxed_1595_ = lean_unbox(v___x_1580_);
v_res_1596_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3(v___y_17168__boxed_1593_, v_xs2_1570_, v___x_1571_, v_ysx2_1572_, v___x_1573_, v___x_1574_, v_val_1575_, v_j_1576_, v_P_1577_, v_xs1_1578_, v_isZero_boxed_1594_, v___x_17173__boxed_1595_, v_indName_1581_, v___x_1582_, v_tail_1583_, v___x_1584_, v___f_1585_, v_zs1_1586_, v_x_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec_ref(v_x_1587_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(lean_object* v_P_1597_, lean_object* v_x_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1604_, 0, v_P_1597_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed(lean_object* v_P_1605_, lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0(v_P_1605_, v_x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v_x_1606_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(lean_object* v_val_1613_, lean_object* v_P_1614_, lean_object* v_xs1_1615_, lean_object* v_xs2_1616_, lean_object* v_indName_1617_, lean_object* v___x_1618_, lean_object* v___x_1619_, lean_object* v_ysx2_1620_, uint8_t v___y_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v_tail_1624_, lean_object* v___x_1625_, lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_j_1628_, lean_object* v_bs_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_zero_1635_; uint8_t v_isZero_1636_; 
v_zero_1635_ = lean_unsigned_to_nat(0u);
v_isZero_1636_ = lean_nat_dec_eq(v_i_1627_, v_zero_1635_);
if (v_isZero_1636_ == 1)
{
lean_object* v___x_1637_; 
lean_dec(v_j_1628_);
lean_dec(v_i_1627_);
lean_dec_ref(v___x_1625_);
lean_dec(v_tail_1624_);
lean_dec(v___x_1623_);
lean_dec_ref(v___x_1622_);
lean_dec_ref(v_ysx2_1620_);
lean_dec_ref(v___x_1619_);
lean_dec(v___x_1618_);
lean_dec(v_indName_1617_);
lean_dec_ref(v_xs2_1616_);
lean_dec_ref(v_xs1_1615_);
lean_dec_ref(v_P_1614_);
lean_dec_ref(v_val_1613_);
v___x_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1637_, 0, v_bs_1629_);
return v___x_1637_;
}
else
{
lean_object* v___f_1638_; uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
lean_inc_ref_n(v_P_1614_, 2);
v___f_1638_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1638_, 0, v_P_1614_);
v___x_1639_ = 1;
v___x_1640_ = lean_box(v___y_1621_);
v___x_1641_ = lean_box(v_isZero_1636_);
v___x_1642_ = lean_box(v___x_1639_);
lean_inc_ref(v___x_1625_);
lean_inc(v_tail_1624_);
lean_inc(v___x_1618_);
lean_inc(v_indName_1617_);
lean_inc_ref(v_xs1_1615_);
lean_inc(v_j_1628_);
lean_inc_ref(v_val_1613_);
lean_inc(v___x_1623_);
lean_inc_ref(v___x_1622_);
lean_inc_ref(v_ysx2_1620_);
lean_inc_ref(v___x_1619_);
lean_inc_ref(v_xs2_1616_);
v___f_1643_ = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___lam__3___boxed), 24, 17);
lean_closure_set(v___f_1643_, 0, v___x_1640_);
lean_closure_set(v___f_1643_, 1, v_xs2_1616_);
lean_closure_set(v___f_1643_, 2, v___x_1619_);
lean_closure_set(v___f_1643_, 3, v_ysx2_1620_);
lean_closure_set(v___f_1643_, 4, v___x_1622_);
lean_closure_set(v___f_1643_, 5, v___x_1623_);
lean_closure_set(v___f_1643_, 6, v_val_1613_);
lean_closure_set(v___f_1643_, 7, v_j_1628_);
lean_closure_set(v___f_1643_, 8, v_P_1614_);
lean_closure_set(v___f_1643_, 9, v_xs1_1615_);
lean_closure_set(v___f_1643_, 10, v___x_1641_);
lean_closure_set(v___f_1643_, 11, v___x_1642_);
lean_closure_set(v___f_1643_, 12, v_indName_1617_);
lean_closure_set(v___f_1643_, 13, v___x_1618_);
lean_closure_set(v___f_1643_, 14, v_tail_1624_);
lean_closure_set(v___f_1643_, 15, v___x_1625_);
lean_closure_set(v___f_1643_, 16, v___f_1638_);
v___x_1644_ = lean_array_fget_borrowed(v_as_1626_, v_j_1628_);
lean_inc(v___x_1644_);
v___x_1645_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1644_, v___f_1643_, v_isZero_1636_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_one_1647_; lean_object* v_n_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v_one_1647_ = lean_unsigned_to_nat(1u);
v_n_1648_ = lean_nat_sub(v_i_1627_, v_one_1647_);
lean_dec(v_i_1627_);
v___x_1649_ = lean_nat_add(v_j_1628_, v_one_1647_);
lean_dec(v_j_1628_);
v___x_1650_ = lean_array_push(v_bs_1629_, v_a_1646_);
v_i_1627_ = v_n_1648_;
v_j_1628_ = v___x_1649_;
v_bs_1629_ = v___x_1650_;
goto _start;
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_bs_1629_);
lean_dec(v_j_1628_);
lean_dec(v_i_1627_);
lean_dec_ref(v___x_1625_);
lean_dec(v_tail_1624_);
lean_dec(v___x_1623_);
lean_dec_ref(v___x_1622_);
lean_dec_ref(v_ysx2_1620_);
lean_dec_ref(v___x_1619_);
lean_dec(v___x_1618_);
lean_dec(v_indName_1617_);
lean_dec_ref(v_xs2_1616_);
lean_dec_ref(v_xs1_1615_);
lean_dec_ref(v_P_1614_);
lean_dec_ref(v_val_1613_);
v_a_1652_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1645_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1645_);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_val_1660_ = _args[0];
lean_object* v_P_1661_ = _args[1];
lean_object* v_xs1_1662_ = _args[2];
lean_object* v_xs2_1663_ = _args[3];
lean_object* v_indName_1664_ = _args[4];
lean_object* v___x_1665_ = _args[5];
lean_object* v___x_1666_ = _args[6];
lean_object* v_ysx2_1667_ = _args[7];
lean_object* v___y_1668_ = _args[8];
lean_object* v___x_1669_ = _args[9];
lean_object* v___x_1670_ = _args[10];
lean_object* v_tail_1671_ = _args[11];
lean_object* v___x_1672_ = _args[12];
lean_object* v_as_1673_ = _args[13];
lean_object* v_i_1674_ = _args[14];
lean_object* v_j_1675_ = _args[15];
lean_object* v_bs_1676_ = _args[16];
lean_object* v___y_1677_ = _args[17];
lean_object* v___y_1678_ = _args[18];
lean_object* v___y_1679_ = _args[19];
lean_object* v___y_1680_ = _args[20];
lean_object* v___y_1681_ = _args[21];
_start:
{
uint8_t v___y_17331__boxed_1682_; lean_object* v_res_1683_; 
v___y_17331__boxed_1682_ = lean_unbox(v___y_1668_);
v_res_1683_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1660_, v_P_1661_, v_xs1_1662_, v_xs2_1663_, v_indName_1664_, v___x_1665_, v___x_1666_, v_ysx2_1667_, v___y_17331__boxed_1682_, v___x_1669_, v___x_1670_, v_tail_1671_, v___x_1672_, v_as_1673_, v_i_1674_, v_j_1675_, v_bs_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_as_1673_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(lean_object* v___x_1684_, lean_object* v_t1_1685_, lean_object* v_val_1686_, lean_object* v_P_1687_, lean_object* v_xs1_1688_, lean_object* v_xs2_1689_, lean_object* v_indName_1690_, lean_object* v___x_1691_, lean_object* v___x_1692_, lean_object* v_ysx2_1693_, uint8_t v___y_1694_, lean_object* v___x_1695_, lean_object* v_tail_1696_, lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v___x_1699_, lean_object* v_ysx1_1700_, uint8_t v___x_1701_, uint8_t v___x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
lean_inc(v___x_1684_);
v___x_1708_ = l_Lean_Meta_arrowDomainsN(v___x_1684_, v_t1_1685_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_array_get_size(v_a_1709_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_mk_empty_array_with_capacity(v___x_1710_);
lean_inc_ref(v_ysx2_1693_);
lean_inc_ref(v_xs2_1689_);
lean_inc_ref(v_xs1_1688_);
lean_inc_ref(v_P_1687_);
v___x_1713_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_1686_, v_P_1687_, v_xs1_1688_, v_xs2_1689_, v_indName_1690_, v___x_1691_, v___x_1692_, v_ysx2_1693_, v___y_1694_, v___x_1695_, v___x_1684_, v_tail_1696_, v___x_1697_, v_a_1709_, v___x_1710_, v___x_1711_, v___x_1712_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v_a_1709_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
v___x_1715_ = l_Lean_mkAppN(v___x_1698_, v_a_1714_);
lean_dec(v_a_1714_);
v___x_1716_ = lean_array_push(v___x_1699_, v_P_1687_);
v___x_1717_ = l_Array_append___redArg(v___x_1716_, v_xs1_1688_);
lean_dec_ref(v_xs1_1688_);
v___x_1718_ = l_Array_append___redArg(v___x_1717_, v_ysx1_1700_);
v___x_1719_ = l_Array_append___redArg(v___x_1718_, v_xs2_1689_);
lean_dec_ref(v_xs2_1689_);
v___x_1720_ = l_Array_append___redArg(v___x_1719_, v_ysx2_1693_);
lean_dec_ref(v_ysx2_1693_);
v___x_1721_ = 1;
v___x_1722_ = l_Lean_Meta_mkLambdaFVars(v___x_1720_, v___x_1715_, v___x_1701_, v___x_1702_, v___x_1701_, v___x_1702_, v___x_1721_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec_ref(v___x_1720_);
return v___x_1722_;
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
lean_dec_ref(v_ysx2_1693_);
lean_dec_ref(v_xs2_1689_);
lean_dec_ref(v_xs1_1688_);
lean_dec_ref(v_P_1687_);
v_a_1723_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1713_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1713_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___x_1699_);
lean_dec_ref(v___x_1698_);
lean_dec_ref(v___x_1697_);
lean_dec(v_tail_1696_);
lean_dec_ref(v___x_1695_);
lean_dec_ref(v_ysx2_1693_);
lean_dec_ref(v___x_1692_);
lean_dec(v___x_1691_);
lean_dec(v_indName_1690_);
lean_dec_ref(v_xs2_1689_);
lean_dec_ref(v_xs1_1688_);
lean_dec_ref(v_P_1687_);
lean_dec_ref(v_val_1686_);
lean_dec(v___x_1684_);
v_a_1731_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1708_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1708_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed(lean_object** _args){
lean_object* v___x_1739_ = _args[0];
lean_object* v_t1_1740_ = _args[1];
lean_object* v_val_1741_ = _args[2];
lean_object* v_P_1742_ = _args[3];
lean_object* v_xs1_1743_ = _args[4];
lean_object* v_xs2_1744_ = _args[5];
lean_object* v_indName_1745_ = _args[6];
lean_object* v___x_1746_ = _args[7];
lean_object* v___x_1747_ = _args[8];
lean_object* v_ysx2_1748_ = _args[9];
lean_object* v___y_1749_ = _args[10];
lean_object* v___x_1750_ = _args[11];
lean_object* v_tail_1751_ = _args[12];
lean_object* v___x_1752_ = _args[13];
lean_object* v___x_1753_ = _args[14];
lean_object* v___x_1754_ = _args[15];
lean_object* v_ysx1_1755_ = _args[16];
lean_object* v___x_1756_ = _args[17];
lean_object* v___x_1757_ = _args[18];
lean_object* v___y_1758_ = _args[19];
lean_object* v___y_1759_ = _args[20];
lean_object* v___y_1760_ = _args[21];
lean_object* v___y_1761_ = _args[22];
lean_object* v___y_1762_ = _args[23];
_start:
{
uint8_t v___y_17415__boxed_1763_; uint8_t v___x_17421__boxed_1764_; uint8_t v___x_17422__boxed_1765_; lean_object* v_res_1766_; 
v___y_17415__boxed_1763_ = lean_unbox(v___y_1749_);
v___x_17421__boxed_1764_ = lean_unbox(v___x_1756_);
v___x_17422__boxed_1765_ = lean_unbox(v___x_1757_);
v_res_1766_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1(v___x_1739_, v_t1_1740_, v_val_1741_, v_P_1742_, v_xs1_1743_, v_xs2_1744_, v_indName_1745_, v___x_1746_, v___x_1747_, v_ysx2_1748_, v___y_17415__boxed_1763_, v___x_1750_, v_tail_1751_, v___x_1752_, v___x_1753_, v___x_1754_, v_ysx1_1755_, v___x_17421__boxed_1764_, v___x_17422__boxed_1765_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec_ref(v_ysx1_1755_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(lean_object* v___x_1767_, lean_object* v_ysx1_1768_, lean_object* v___x_1769_, lean_object* v_t1_1770_, lean_object* v_val_1771_, lean_object* v_P_1772_, lean_object* v_xs1_1773_, lean_object* v_xs2_1774_, lean_object* v_indName_1775_, lean_object* v___x_1776_, lean_object* v___x_1777_, uint8_t v___y_1778_, lean_object* v___x_1779_, lean_object* v_tail_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, uint8_t v___x_1783_, uint8_t v___x_1784_, lean_object* v_ysx2_1785_, lean_object* v___t2_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; 
v___x_1792_ = l_Lean_mkAppN(v___x_1767_, v_ysx1_1768_);
v___x_1793_ = lean_box(v___y_1778_);
v___x_1794_ = lean_box(v___x_1783_);
v___x_1795_ = lean_box(v___x_1784_);
lean_inc_ref(v_ysx2_1785_);
v___f_1796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1796_, 0, v___x_1769_);
lean_closure_set(v___f_1796_, 1, v_t1_1770_);
lean_closure_set(v___f_1796_, 2, v_val_1771_);
lean_closure_set(v___f_1796_, 3, v_P_1772_);
lean_closure_set(v___f_1796_, 4, v_xs1_1773_);
lean_closure_set(v___f_1796_, 5, v_xs2_1774_);
lean_closure_set(v___f_1796_, 6, v_indName_1775_);
lean_closure_set(v___f_1796_, 7, v___x_1776_);
lean_closure_set(v___f_1796_, 8, v___x_1777_);
lean_closure_set(v___f_1796_, 9, v_ysx2_1785_);
lean_closure_set(v___f_1796_, 10, v___x_1793_);
lean_closure_set(v___f_1796_, 11, v___x_1779_);
lean_closure_set(v___f_1796_, 12, v_tail_1780_);
lean_closure_set(v___f_1796_, 13, v___x_1781_);
lean_closure_set(v___f_1796_, 14, v___x_1792_);
lean_closure_set(v___f_1796_, 15, v___x_1782_);
lean_closure_set(v___f_1796_, 16, v_ysx1_1768_);
lean_closure_set(v___f_1796_, 17, v___x_1794_);
lean_closure_set(v___f_1796_, 18, v___x_1795_);
v___x_1797_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_ysx2_1785_, v___f_1796_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed(lean_object** _args){
lean_object* v___x_1798_ = _args[0];
lean_object* v_ysx1_1799_ = _args[1];
lean_object* v___x_1800_ = _args[2];
lean_object* v_t1_1801_ = _args[3];
lean_object* v_val_1802_ = _args[4];
lean_object* v_P_1803_ = _args[5];
lean_object* v_xs1_1804_ = _args[6];
lean_object* v_xs2_1805_ = _args[7];
lean_object* v_indName_1806_ = _args[8];
lean_object* v___x_1807_ = _args[9];
lean_object* v___x_1808_ = _args[10];
lean_object* v___y_1809_ = _args[11];
lean_object* v___x_1810_ = _args[12];
lean_object* v_tail_1811_ = _args[13];
lean_object* v___x_1812_ = _args[14];
lean_object* v___x_1813_ = _args[15];
lean_object* v___x_1814_ = _args[16];
lean_object* v___x_1815_ = _args[17];
lean_object* v_ysx2_1816_ = _args[18];
lean_object* v___t2_1817_ = _args[19];
lean_object* v___y_1818_ = _args[20];
lean_object* v___y_1819_ = _args[21];
lean_object* v___y_1820_ = _args[22];
lean_object* v___y_1821_ = _args[23];
lean_object* v___y_1822_ = _args[24];
_start:
{
uint8_t v___y_17529__boxed_1823_; uint8_t v___x_17534__boxed_1824_; uint8_t v___x_17535__boxed_1825_; lean_object* v_res_1826_; 
v___y_17529__boxed_1823_ = lean_unbox(v___y_1809_);
v___x_17534__boxed_1824_ = lean_unbox(v___x_1814_);
v___x_17535__boxed_1825_ = lean_unbox(v___x_1815_);
v_res_1826_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2(v___x_1798_, v_ysx1_1799_, v___x_1800_, v_t1_1801_, v_val_1802_, v_P_1803_, v_xs1_1804_, v_xs2_1805_, v_indName_1806_, v___x_1807_, v___x_1808_, v___y_17529__boxed_1823_, v___x_1810_, v_tail_1811_, v___x_1812_, v___x_1813_, v___x_17534__boxed_1824_, v___x_17535__boxed_1825_, v_ysx2_1816_, v___t2_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec_ref(v___t2_1817_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v_val_1829_, lean_object* v_P_1830_, lean_object* v_xs1_1831_, lean_object* v_xs2_1832_, lean_object* v_indName_1833_, lean_object* v___x_1834_, lean_object* v___x_1835_, uint8_t v___y_1836_, lean_object* v___x_1837_, lean_object* v_tail_1838_, lean_object* v___x_1839_, lean_object* v___x_1840_, uint8_t v___x_1841_, uint8_t v___x_1842_, lean_object* v_a_1843_, lean_object* v___x_1844_, lean_object* v_ysx1_1845_, lean_object* v_t1_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___f_1855_; lean_object* v___x_1856_; 
v___x_1852_ = lean_box(v___y_1836_);
v___x_1853_ = lean_box(v___x_1841_);
v___x_1854_ = lean_box(v___x_1842_);
v___f_1855_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__2___boxed), 25, 18);
lean_closure_set(v___f_1855_, 0, v___x_1827_);
lean_closure_set(v___f_1855_, 1, v_ysx1_1845_);
lean_closure_set(v___f_1855_, 2, v___x_1828_);
lean_closure_set(v___f_1855_, 3, v_t1_1846_);
lean_closure_set(v___f_1855_, 4, v_val_1829_);
lean_closure_set(v___f_1855_, 5, v_P_1830_);
lean_closure_set(v___f_1855_, 6, v_xs1_1831_);
lean_closure_set(v___f_1855_, 7, v_xs2_1832_);
lean_closure_set(v___f_1855_, 8, v_indName_1833_);
lean_closure_set(v___f_1855_, 9, v___x_1834_);
lean_closure_set(v___f_1855_, 10, v___x_1835_);
lean_closure_set(v___f_1855_, 11, v___x_1852_);
lean_closure_set(v___f_1855_, 12, v___x_1837_);
lean_closure_set(v___f_1855_, 13, v_tail_1838_);
lean_closure_set(v___f_1855_, 14, v___x_1839_);
lean_closure_set(v___f_1855_, 15, v___x_1840_);
lean_closure_set(v___f_1855_, 16, v___x_1853_);
lean_closure_set(v___f_1855_, 17, v___x_1854_);
v___x_1856_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1843_, v___x_1844_, v___f_1855_, v___x_1841_, v___x_1841_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed(lean_object** _args){
lean_object* v___x_1857_ = _args[0];
lean_object* v___x_1858_ = _args[1];
lean_object* v_val_1859_ = _args[2];
lean_object* v_P_1860_ = _args[3];
lean_object* v_xs1_1861_ = _args[4];
lean_object* v_xs2_1862_ = _args[5];
lean_object* v_indName_1863_ = _args[6];
lean_object* v___x_1864_ = _args[7];
lean_object* v___x_1865_ = _args[8];
lean_object* v___y_1866_ = _args[9];
lean_object* v___x_1867_ = _args[10];
lean_object* v_tail_1868_ = _args[11];
lean_object* v___x_1869_ = _args[12];
lean_object* v___x_1870_ = _args[13];
lean_object* v___x_1871_ = _args[14];
lean_object* v___x_1872_ = _args[15];
lean_object* v_a_1873_ = _args[16];
lean_object* v___x_1874_ = _args[17];
lean_object* v_ysx1_1875_ = _args[18];
lean_object* v_t1_1876_ = _args[19];
lean_object* v___y_1877_ = _args[20];
lean_object* v___y_1878_ = _args[21];
lean_object* v___y_1879_ = _args[22];
lean_object* v___y_1880_ = _args[23];
lean_object* v___y_1881_ = _args[24];
_start:
{
uint8_t v___y_17592__boxed_1882_; uint8_t v___x_17597__boxed_1883_; uint8_t v___x_17598__boxed_1884_; lean_object* v_res_1885_; 
v___y_17592__boxed_1882_ = lean_unbox(v___y_1866_);
v___x_17597__boxed_1883_ = lean_unbox(v___x_1871_);
v___x_17598__boxed_1884_ = lean_unbox(v___x_1872_);
v_res_1885_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3(v___x_1857_, v___x_1858_, v_val_1859_, v_P_1860_, v_xs1_1861_, v_xs2_1862_, v_indName_1863_, v___x_1864_, v___x_1865_, v___y_17592__boxed_1882_, v___x_1867_, v_tail_1868_, v___x_1869_, v___x_1870_, v___x_17597__boxed_1883_, v___x_17598__boxed_1884_, v_a_1873_, v___x_1874_, v_ysx1_1875_, v_t1_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(lean_object* v_t1_1886_, lean_object* v___f_1887_, lean_object* v_t2_1888_, lean_object* v___x_1889_, lean_object* v_numIndices_1890_, lean_object* v___x_1891_, lean_object* v_val_1892_, lean_object* v_P_1893_, lean_object* v_xs1_1894_, lean_object* v_xs2_1895_, lean_object* v_indName_1896_, lean_object* v___x_1897_, uint8_t v___y_1898_, lean_object* v___x_1899_, lean_object* v_tail_1900_, lean_object* v___x_1901_, uint8_t v___x_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; 
lean_inc_ref(v_t1_1886_);
v___x_1908_ = l_Lean_Meta_whnfD(v_t1_1886_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = l_Lean_Expr_bindingDomain_x21(v_a_1909_);
lean_dec(v_a_1909_);
v___x_1911_ = 0;
lean_inc_ref(v___f_1887_);
v___x_1912_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1910_, v___f_1887_, v___x_1911_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc_n(v_a_1913_, 2);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1914_);
lean_inc_ref(v___x_1915_);
v___x_1916_ = lean_array_push(v___x_1915_, v_a_1913_);
v___x_1917_ = l_Lean_Meta_instantiateForall(v_t1_1886_, v___x_1916_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec_ref(v___x_1916_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
lean_inc_ref(v_t2_1888_);
v___x_1919_ = l_Lean_Meta_whnfD(v_t2_1888_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = l_Lean_Expr_bindingDomain_x21(v_a_1920_);
lean_dec(v_a_1920_);
v___x_1922_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__3___redArg(v___x_1921_, v___f_1887_, v___x_1911_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
lean_inc_ref(v___x_1915_);
v___x_1924_ = lean_array_push(v___x_1915_, v_a_1923_);
v___x_1925_ = l_Lean_Meta_instantiateForall(v_t2_1888_, v___x_1924_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1940_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = l_Lean_Expr_app___override(v___x_1889_, v_a_1913_);
v___x_1931_ = lean_nat_add(v_numIndices_1890_, v___x_1914_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set_tag(v___x_1928_, 1);
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___f_1937_; lean_object* v___x_1938_; 
v___x_1934_ = lean_box(v___y_1898_);
v___x_1935_ = lean_box(v___x_1911_);
v___x_1936_ = lean_box(v___x_1902_);
lean_inc_ref(v___x_1933_);
v___f_1937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__3___boxed), 25, 18);
lean_closure_set(v___f_1937_, 0, v___x_1930_);
lean_closure_set(v___f_1937_, 1, v___x_1891_);
lean_closure_set(v___f_1937_, 2, v_val_1892_);
lean_closure_set(v___f_1937_, 3, v_P_1893_);
lean_closure_set(v___f_1937_, 4, v_xs1_1894_);
lean_closure_set(v___f_1937_, 5, v_xs2_1895_);
lean_closure_set(v___f_1937_, 6, v_indName_1896_);
lean_closure_set(v___f_1937_, 7, v___x_1897_);
lean_closure_set(v___f_1937_, 8, v___x_1924_);
lean_closure_set(v___f_1937_, 9, v___x_1934_);
lean_closure_set(v___f_1937_, 10, v___x_1899_);
lean_closure_set(v___f_1937_, 11, v_tail_1900_);
lean_closure_set(v___f_1937_, 12, v___x_1901_);
lean_closure_set(v___f_1937_, 13, v___x_1915_);
lean_closure_set(v___f_1937_, 14, v___x_1935_);
lean_closure_set(v___f_1937_, 15, v___x_1936_);
lean_closure_set(v___f_1937_, 16, v_a_1926_);
lean_closure_set(v___f_1937_, 17, v___x_1933_);
v___x_1938_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_1918_, v___x_1933_, v___f_1937_, v___x_1911_, v___x_1911_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
return v___x_1938_;
}
}
}
else
{
lean_dec_ref(v___x_1924_);
lean_dec(v_a_1918_);
lean_dec_ref(v___x_1915_);
lean_dec(v_a_1913_);
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
return v___x_1925_;
}
}
else
{
lean_dec(v_a_1918_);
lean_dec_ref(v___x_1915_);
lean_dec(v_a_1913_);
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_t2_1888_);
return v___x_1922_;
}
}
else
{
lean_dec(v_a_1918_);
lean_dec_ref(v___x_1915_);
lean_dec(v_a_1913_);
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_t2_1888_);
lean_dec_ref(v___f_1887_);
return v___x_1919_;
}
}
else
{
lean_dec_ref(v___x_1915_);
lean_dec(v_a_1913_);
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_t2_1888_);
lean_dec_ref(v___f_1887_);
return v___x_1917_;
}
}
else
{
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_t2_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_t1_1886_);
return v___x_1912_;
}
}
else
{
lean_dec_ref(v___x_1901_);
lean_dec(v_tail_1900_);
lean_dec_ref(v___x_1899_);
lean_dec(v___x_1897_);
lean_dec(v_indName_1896_);
lean_dec_ref(v_xs2_1895_);
lean_dec_ref(v_xs1_1894_);
lean_dec_ref(v_P_1893_);
lean_dec_ref(v_val_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1889_);
lean_dec_ref(v_t2_1888_);
lean_dec_ref(v___f_1887_);
lean_dec_ref(v_t1_1886_);
return v___x_1908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed(lean_object** _args){
lean_object* v_t1_1941_ = _args[0];
lean_object* v___f_1942_ = _args[1];
lean_object* v_t2_1943_ = _args[2];
lean_object* v___x_1944_ = _args[3];
lean_object* v_numIndices_1945_ = _args[4];
lean_object* v___x_1946_ = _args[5];
lean_object* v_val_1947_ = _args[6];
lean_object* v_P_1948_ = _args[7];
lean_object* v_xs1_1949_ = _args[8];
lean_object* v_xs2_1950_ = _args[9];
lean_object* v_indName_1951_ = _args[10];
lean_object* v___x_1952_ = _args[11];
lean_object* v___y_1953_ = _args[12];
lean_object* v___x_1954_ = _args[13];
lean_object* v_tail_1955_ = _args[14];
lean_object* v___x_1956_ = _args[15];
lean_object* v___x_1957_ = _args[16];
lean_object* v___y_1958_ = _args[17];
lean_object* v___y_1959_ = _args[18];
lean_object* v___y_1960_ = _args[19];
lean_object* v___y_1961_ = _args[20];
lean_object* v___y_1962_ = _args[21];
_start:
{
uint8_t v___y_17659__boxed_1963_; uint8_t v___x_17663__boxed_1964_; lean_object* v_res_1965_; 
v___y_17659__boxed_1963_ = lean_unbox(v___y_1953_);
v___x_17663__boxed_1964_ = lean_unbox(v___x_1957_);
v_res_1965_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4(v_t1_1941_, v___f_1942_, v_t2_1943_, v___x_1944_, v_numIndices_1945_, v___x_1946_, v_val_1947_, v_P_1948_, v_xs1_1949_, v_xs2_1950_, v_indName_1951_, v___x_1952_, v___y_17659__boxed_1963_, v___x_1954_, v_tail_1955_, v___x_1956_, v___x_17663__boxed_1964_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_numIndices_1945_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(lean_object* v___x_1966_, lean_object* v_xs1_1967_, lean_object* v_t1_1968_, lean_object* v___f_1969_, lean_object* v_numIndices_1970_, lean_object* v___x_1971_, lean_object* v_val_1972_, lean_object* v_P_1973_, lean_object* v_indName_1974_, lean_object* v___x_1975_, uint8_t v___y_1976_, lean_object* v_tail_1977_, lean_object* v___x_1978_, uint8_t v___x_1979_, lean_object* v_xs2_1980_, lean_object* v_t2_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; 
lean_inc_ref(v___x_1966_);
v___x_1987_ = l_Lean_mkAppN(v___x_1966_, v_xs1_1967_);
v___x_1988_ = lean_box(v___y_1976_);
v___x_1989_ = lean_box(v___x_1979_);
lean_inc_ref(v_xs2_1980_);
v___f_1990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__4___boxed), 22, 17);
lean_closure_set(v___f_1990_, 0, v_t1_1968_);
lean_closure_set(v___f_1990_, 1, v___f_1969_);
lean_closure_set(v___f_1990_, 2, v_t2_1981_);
lean_closure_set(v___f_1990_, 3, v___x_1987_);
lean_closure_set(v___f_1990_, 4, v_numIndices_1970_);
lean_closure_set(v___f_1990_, 5, v___x_1971_);
lean_closure_set(v___f_1990_, 6, v_val_1972_);
lean_closure_set(v___f_1990_, 7, v_P_1973_);
lean_closure_set(v___f_1990_, 8, v_xs1_1967_);
lean_closure_set(v___f_1990_, 9, v_xs2_1980_);
lean_closure_set(v___f_1990_, 10, v_indName_1974_);
lean_closure_set(v___f_1990_, 11, v___x_1975_);
lean_closure_set(v___f_1990_, 12, v___x_1988_);
lean_closure_set(v___f_1990_, 13, v___x_1966_);
lean_closure_set(v___f_1990_, 14, v_tail_1977_);
lean_closure_set(v___f_1990_, 15, v___x_1978_);
lean_closure_set(v___f_1990_, 16, v___x_1989_);
v___x_1991_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_xs2_1980_, v___f_1990_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed(lean_object** _args){
lean_object* v___x_1992_ = _args[0];
lean_object* v_xs1_1993_ = _args[1];
lean_object* v_t1_1994_ = _args[2];
lean_object* v___f_1995_ = _args[3];
lean_object* v_numIndices_1996_ = _args[4];
lean_object* v___x_1997_ = _args[5];
lean_object* v_val_1998_ = _args[6];
lean_object* v_P_1999_ = _args[7];
lean_object* v_indName_2000_ = _args[8];
lean_object* v___x_2001_ = _args[9];
lean_object* v___y_2002_ = _args[10];
lean_object* v_tail_2003_ = _args[11];
lean_object* v___x_2004_ = _args[12];
lean_object* v___x_2005_ = _args[13];
lean_object* v_xs2_2006_ = _args[14];
lean_object* v_t2_2007_ = _args[15];
lean_object* v___y_2008_ = _args[16];
lean_object* v___y_2009_ = _args[17];
lean_object* v___y_2010_ = _args[18];
lean_object* v___y_2011_ = _args[19];
lean_object* v___y_2012_ = _args[20];
_start:
{
uint8_t v___y_17776__boxed_2013_; uint8_t v___x_17779__boxed_2014_; lean_object* v_res_2015_; 
v___y_17776__boxed_2013_ = lean_unbox(v___y_2002_);
v___x_17779__boxed_2014_ = lean_unbox(v___x_2005_);
v_res_2015_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5(v___x_1992_, v_xs1_1993_, v_t1_1994_, v___f_1995_, v_numIndices_1996_, v___x_1997_, v_val_1998_, v_P_1999_, v_indName_2000_, v___x_2001_, v___y_17776__boxed_2013_, v_tail_2003_, v___x_2004_, v___x_17779__boxed_2014_, v_xs2_2006_, v_t2_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(lean_object* v___x_2016_, lean_object* v___f_2017_, lean_object* v_numIndices_2018_, lean_object* v___x_2019_, lean_object* v_val_2020_, lean_object* v_P_2021_, lean_object* v_indName_2022_, lean_object* v___x_2023_, uint8_t v___y_2024_, lean_object* v_tail_2025_, lean_object* v___x_2026_, uint8_t v___x_2027_, lean_object* v_a_2028_, lean_object* v___x_2029_, lean_object* v_xs1_2030_, lean_object* v_t1_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2037_ = lean_box(v___y_2024_);
v___x_2038_ = lean_box(v___x_2027_);
v___f_2039_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__5___boxed), 21, 14);
lean_closure_set(v___f_2039_, 0, v___x_2016_);
lean_closure_set(v___f_2039_, 1, v_xs1_2030_);
lean_closure_set(v___f_2039_, 2, v_t1_2031_);
lean_closure_set(v___f_2039_, 3, v___f_2017_);
lean_closure_set(v___f_2039_, 4, v_numIndices_2018_);
lean_closure_set(v___f_2039_, 5, v___x_2019_);
lean_closure_set(v___f_2039_, 6, v_val_2020_);
lean_closure_set(v___f_2039_, 7, v_P_2021_);
lean_closure_set(v___f_2039_, 8, v_indName_2022_);
lean_closure_set(v___f_2039_, 9, v___x_2023_);
lean_closure_set(v___f_2039_, 10, v___x_2037_);
lean_closure_set(v___f_2039_, 11, v_tail_2025_);
lean_closure_set(v___f_2039_, 12, v___x_2026_);
lean_closure_set(v___f_2039_, 13, v___x_2038_);
v___x_2040_ = 0;
v___x_2041_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2028_, v___x_2029_, v___f_2039_, v___x_2040_, v___x_2040_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed(lean_object** _args){
lean_object* v___x_2042_ = _args[0];
lean_object* v___f_2043_ = _args[1];
lean_object* v_numIndices_2044_ = _args[2];
lean_object* v___x_2045_ = _args[3];
lean_object* v_val_2046_ = _args[4];
lean_object* v_P_2047_ = _args[5];
lean_object* v_indName_2048_ = _args[6];
lean_object* v___x_2049_ = _args[7];
lean_object* v___y_2050_ = _args[8];
lean_object* v_tail_2051_ = _args[9];
lean_object* v___x_2052_ = _args[10];
lean_object* v___x_2053_ = _args[11];
lean_object* v_a_2054_ = _args[12];
lean_object* v___x_2055_ = _args[13];
lean_object* v_xs1_2056_ = _args[14];
lean_object* v_t1_2057_ = _args[15];
lean_object* v___y_2058_ = _args[16];
lean_object* v___y_2059_ = _args[17];
lean_object* v___y_2060_ = _args[18];
lean_object* v___y_2061_ = _args[19];
lean_object* v___y_2062_ = _args[20];
_start:
{
uint8_t v___y_17828__boxed_2063_; uint8_t v___x_17831__boxed_2064_; lean_object* v_res_2065_; 
v___y_17828__boxed_2063_ = lean_unbox(v___y_2050_);
v___x_17831__boxed_2064_ = lean_unbox(v___x_2053_);
v_res_2065_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6(v___x_2042_, v___f_2043_, v_numIndices_2044_, v___x_2045_, v_val_2046_, v_P_2047_, v_indName_2048_, v___x_2049_, v___y_17828__boxed_2063_, v_tail_2051_, v___x_2052_, v___x_17831__boxed_2064_, v_a_2054_, v___x_2055_, v_xs1_2056_, v_t1_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(lean_object* v_val_2066_, lean_object* v___x_2067_, lean_object* v___f_2068_, lean_object* v___x_2069_, lean_object* v_indName_2070_, lean_object* v___x_2071_, uint8_t v___y_2072_, lean_object* v_tail_2073_, lean_object* v___x_2074_, uint8_t v___x_2075_, lean_object* v_a_2076_, lean_object* v_P_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_numParams_2083_; lean_object* v_numIndices_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___f_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v_numParams_2083_ = lean_ctor_get(v_val_2066_, 1);
v_numIndices_2084_ = lean_ctor_get(v_val_2066_, 2);
lean_inc(v_numIndices_2084_);
lean_inc(v_numParams_2083_);
v___x_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_numParams_2083_);
v___x_2086_ = lean_box(v___y_2072_);
v___x_2087_ = lean_box(v___x_2075_);
lean_inc_ref(v___x_2085_);
lean_inc_ref(v_a_2076_);
v___f_2088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__6___boxed), 21, 14);
lean_closure_set(v___f_2088_, 0, v___x_2067_);
lean_closure_set(v___f_2088_, 1, v___f_2068_);
lean_closure_set(v___f_2088_, 2, v_numIndices_2084_);
lean_closure_set(v___f_2088_, 3, v___x_2069_);
lean_closure_set(v___f_2088_, 4, v_val_2066_);
lean_closure_set(v___f_2088_, 5, v_P_2077_);
lean_closure_set(v___f_2088_, 6, v_indName_2070_);
lean_closure_set(v___f_2088_, 7, v___x_2071_);
lean_closure_set(v___f_2088_, 8, v___x_2086_);
lean_closure_set(v___f_2088_, 9, v_tail_2073_);
lean_closure_set(v___f_2088_, 10, v___x_2074_);
lean_closure_set(v___f_2088_, 11, v___x_2087_);
lean_closure_set(v___f_2088_, 12, v_a_2076_);
lean_closure_set(v___f_2088_, 13, v___x_2085_);
v___x_2089_ = 0;
v___x_2090_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_a_2076_, v___x_2085_, v___f_2088_, v___x_2089_, v___x_2089_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed(lean_object** _args){
lean_object* v_val_2091_ = _args[0];
lean_object* v___x_2092_ = _args[1];
lean_object* v___f_2093_ = _args[2];
lean_object* v___x_2094_ = _args[3];
lean_object* v_indName_2095_ = _args[4];
lean_object* v___x_2096_ = _args[5];
lean_object* v___y_2097_ = _args[6];
lean_object* v_tail_2098_ = _args[7];
lean_object* v___x_2099_ = _args[8];
lean_object* v___x_2100_ = _args[9];
lean_object* v_a_2101_ = _args[10];
lean_object* v_P_2102_ = _args[11];
lean_object* v___y_2103_ = _args[12];
lean_object* v___y_2104_ = _args[13];
lean_object* v___y_2105_ = _args[14];
lean_object* v___y_2106_ = _args[15];
lean_object* v___y_2107_ = _args[16];
_start:
{
uint8_t v___y_17886__boxed_2108_; uint8_t v___x_17889__boxed_2109_; lean_object* v_res_2110_; 
v___y_17886__boxed_2108_ = lean_unbox(v___y_2097_);
v___x_17889__boxed_2109_ = lean_unbox(v___x_2100_);
v_res_2110_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7(v_val_2091_, v___x_2092_, v___f_2093_, v___x_2094_, v_indName_2095_, v___x_2096_, v___y_17886__boxed_2108_, v_tail_2098_, v___x_2099_, v___x_17889__boxed_2109_, v_a_2101_, v_P_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2110_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__0);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__1);
v___x_2117_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
lean_ctor_set(v___x_2117_, 2, v___x_2116_);
lean_ctor_set(v___x_2117_, 3, v___x_2116_);
lean_ctor_set(v___x_2117_, 4, v___x_2116_);
lean_ctor_set(v___x_2117_, 5, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(lean_object* v_declName_2118_, uint8_t v_s_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v_env_2124_; lean_object* v_nextMacroScope_2125_; lean_object* v_ngen_2126_; lean_object* v_auxDeclNGen_2127_; lean_object* v_traceState_2128_; lean_object* v_messages_2129_; lean_object* v_infoState_2130_; lean_object* v_snapshotTasks_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2160_; 
v___x_2123_ = lean_st_ref_take(v___y_2121_);
v_env_2124_ = lean_ctor_get(v___x_2123_, 0);
v_nextMacroScope_2125_ = lean_ctor_get(v___x_2123_, 1);
v_ngen_2126_ = lean_ctor_get(v___x_2123_, 2);
v_auxDeclNGen_2127_ = lean_ctor_get(v___x_2123_, 3);
v_traceState_2128_ = lean_ctor_get(v___x_2123_, 4);
v_messages_2129_ = lean_ctor_get(v___x_2123_, 6);
v_infoState_2130_ = lean_ctor_get(v___x_2123_, 7);
v_snapshotTasks_2131_ = lean_ctor_get(v___x_2123_, 8);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2123_, 5);
lean_dec(v_unused_2161_);
v___x_2133_ = v___x_2123_;
v_isShared_2134_ = v_isSharedCheck_2160_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_snapshotTasks_2131_);
lean_inc(v_infoState_2130_);
lean_inc(v_messages_2129_);
lean_inc(v_traceState_2128_);
lean_inc(v_auxDeclNGen_2127_);
lean_inc(v_ngen_2126_);
lean_inc(v_nextMacroScope_2125_);
lean_inc(v_env_2124_);
lean_dec(v___x_2123_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2160_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2135_ = 0;
v___x_2136_ = lean_box(0);
v___x_2137_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2124_, v_declName_2118_, v_s_2119_, v___x_2135_, v___x_2136_);
v___x_2138_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 5, v___x_2138_);
lean_ctor_set(v___x_2133_, 0, v___x_2137_);
v___x_2140_ = v___x_2133_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_nextMacroScope_2125_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_ngen_2126_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_auxDeclNGen_2127_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_traceState_2128_);
lean_ctor_set(v_reuseFailAlloc_2159_, 5, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2159_, 6, v_messages_2129_);
lean_ctor_set(v_reuseFailAlloc_2159_, 7, v_infoState_2130_);
lean_ctor_set(v_reuseFailAlloc_2159_, 8, v_snapshotTasks_2131_);
v___x_2140_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_mctx_2143_; lean_object* v_zetaDeltaFVarIds_2144_; lean_object* v_postponed_2145_; lean_object* v_diag_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2157_; 
v___x_2141_ = lean_st_ref_set(v___y_2121_, v___x_2140_);
v___x_2142_ = lean_st_ref_take(v___y_2120_);
v_mctx_2143_ = lean_ctor_get(v___x_2142_, 0);
v_zetaDeltaFVarIds_2144_ = lean_ctor_get(v___x_2142_, 2);
v_postponed_2145_ = lean_ctor_get(v___x_2142_, 3);
v_diag_2146_ = lean_ctor_get(v___x_2142_, 4);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v___x_2142_, 1);
lean_dec(v_unused_2158_);
v___x_2148_ = v___x_2142_;
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_diag_2146_);
lean_inc(v_postponed_2145_);
lean_inc(v_zetaDeltaFVarIds_2144_);
lean_inc(v_mctx_2143_);
lean_dec(v___x_2142_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2157_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_mctx_2143_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_zetaDeltaFVarIds_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_postponed_2145_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_diag_2146_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_st_ref_set(v___y_2120_, v___x_2152_);
v___x_2154_ = lean_box(0);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___boxed(lean_object* v_declName_2162_, lean_object* v_s_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_s_boxed_2167_; lean_object* v_res_2168_; 
v_s_boxed_2167_ = lean_unbox(v_s_2163_);
v_res_2168_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2162_, v_s_boxed_2167_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(lean_object* v_declName_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = 0;
v___x_2176_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2169_, v___x_2175_, v___y_2171_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7___boxed(lean_object* v_declName_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
if (lean_obj_tag(v_a_2184_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = l_List_reverse___redArg(v_a_2185_);
return v___x_2186_;
}
else
{
lean_object* v_head_2187_; lean_object* v_tail_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2197_; 
v_head_2187_ = lean_ctor_get(v_a_2184_, 0);
v_tail_2188_ = lean_ctor_get(v_a_2184_, 1);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2184_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2190_ = v_a_2184_;
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_tail_2188_);
lean_inc(v_head_2187_);
lean_dec(v_a_2184_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2197_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2192_ = l_Lean_mkLevelParam(v_head_2187_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 1, v_a_2185_);
lean_ctor_set(v___x_2190_, 0, v___x_2192_);
v___x_2194_ = v___x_2190_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_a_2185_);
v___x_2194_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
v_a_2184_ = v_tail_2188_;
v_a_2185_ = v___x_2194_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
lean_ctor_set(v___x_2203_, 2, v___x_2202_);
lean_ctor_set(v___x_2203_, 3, v___x_2202_);
lean_ctor_set(v___x_2203_, 4, v___x_2201_);
lean_ctor_set(v___x_2203_, 5, v___x_2201_);
lean_ctor_set(v___x_2203_, 6, v___x_2201_);
lean_ctor_set(v___x_2203_, 7, v___x_2201_);
lean_ctor_set(v___x_2203_, 8, v___x_2201_);
lean_ctor_set(v___x_2203_, 9, v___x_2201_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_unsigned_to_nat(32u);
v___x_2205_ = lean_mk_empty_array_with_capacity(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2207_ = ((size_t)5ULL);
v___x_2208_ = lean_unsigned_to_nat(0u);
v___x_2209_ = lean_unsigned_to_nat(32u);
v___x_2210_ = lean_mk_empty_array_with_capacity(v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_2212_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2210_);
lean_ctor_set(v___x_2212_, 2, v___x_2208_);
lean_ctor_set(v___x_2212_, 3, v___x_2208_);
lean_ctor_set_usize(v___x_2212_, 4, v___x_2207_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_box(1);
v___x_2214_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_2215_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_2216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2213_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_2234_ = l_Lean_stringToMessageData(v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_2237_ = l_Lean_stringToMessageData(v___x_2236_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_2238_, lean_object* v_declHint_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_env_2243_; uint8_t v___x_2244_; 
v___x_2242_ = lean_st_ref_get(v___y_2240_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = l_Lean_Name_isAnonymous(v_declHint_2239_);
if (v___x_2244_ == 0)
{
uint8_t v_isExporting_2245_; 
v_isExporting_2245_ = lean_ctor_get_uint8(v_env_2243_, sizeof(void*)*8);
if (v_isExporting_2245_ == 0)
{
lean_object* v___x_2246_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2239_);
v___x_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_msg_2238_);
return v___x_2246_;
}
else
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
lean_inc_ref(v_env_2243_);
v___x_2247_ = l_Lean_Environment_setExporting(v_env_2243_, v___x_2244_);
lean_inc(v_declHint_2239_);
lean_inc_ref(v___x_2247_);
v___x_2248_ = l_Lean_Environment_contains(v___x_2247_, v_declHint_2239_, v_isExporting_2245_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; 
lean_dec_ref(v___x_2247_);
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2239_);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v_msg_2238_);
return v___x_2249_;
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_c_2255_; lean_object* v___x_2256_; 
v___x_2250_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_2251_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_2252_ = l_Lean_Options_empty;
v___x_2253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2247_);
lean_ctor_set(v___x_2253_, 1, v___x_2250_);
lean_ctor_set(v___x_2253_, 2, v___x_2251_);
lean_ctor_set(v___x_2253_, 3, v___x_2252_);
lean_inc(v_declHint_2239_);
v___x_2254_ = l_Lean_MessageData_ofConstName(v_declHint_2239_, v___x_2244_);
v_c_2255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2255_, 0, v___x_2253_);
lean_ctor_set(v_c_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2243_, v_declHint_2239_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2239_);
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v_c_2255_);
v___x_2259_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_MessageData_note(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v_msg_2238_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2299_; 
v_val_2264_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2266_ = v___x_2256_;
v_isShared_2267_ = v_isSharedCheck_2299_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v___x_2256_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2299_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v_mod_2271_; uint8_t v___x_2272_; 
v___x_2268_ = lean_box(0);
v___x_2269_ = l_Lean_Environment_header(v_env_2243_);
lean_dec_ref(v_env_2243_);
v___x_2270_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2269_);
v_mod_2271_ = lean_array_get(v___x_2268_, v___x_2270_, v_val_2264_);
lean_dec(v_val_2264_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = l_Lean_isPrivateName(v_declHint_2239_);
lean_dec(v_declHint_2239_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v_c_2255_);
v___x_2275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = l_Lean_MessageData_ofName(v_mod_2271_);
v___x_2278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2276_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = l_Lean_MessageData_note(v___x_2280_);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_msg_2238_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2282_);
v___x_2284_ = v___x_2266_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2286_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_2287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_c_2255_);
v___x_2288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2287_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_ofName(v_mod_2271_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_MessageData_note(v___x_2293_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_msg_2238_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2295_);
v___x_2297_ = v___x_2266_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2300_; 
lean_dec_ref(v_env_2243_);
lean_dec(v_declHint_2239_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_msg_2238_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_2301_, lean_object* v_declHint_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2301_, v_declHint_2302_, v___y_2303_);
lean_dec(v___y_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2323_; 
v___x_2313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2306_, v_declHint_2307_, v___y_2311_);
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2323_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2318_ = l_Lean_unknownIdentifierMessageTag;
v___x_2319_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v_a_2314_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2319_);
v___x_2321_ = v___x_2316_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_2324_, lean_object* v_declHint_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2324_, v_declHint_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_2332_, lean_object* v_msg_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_fileName_2339_; lean_object* v_fileMap_2340_; lean_object* v_options_2341_; lean_object* v_currRecDepth_2342_; lean_object* v_maxRecDepth_2343_; lean_object* v_ref_2344_; lean_object* v_currNamespace_2345_; lean_object* v_openDecls_2346_; lean_object* v_initHeartbeats_2347_; lean_object* v_maxHeartbeats_2348_; lean_object* v_quotContext_2349_; lean_object* v_currMacroScope_2350_; uint8_t v_diag_2351_; lean_object* v_cancelTk_x3f_2352_; uint8_t v_suppressElabErrors_2353_; lean_object* v_inheritedTraceOptions_2354_; lean_object* v_ref_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v_fileName_2339_ = lean_ctor_get(v___y_2336_, 0);
v_fileMap_2340_ = lean_ctor_get(v___y_2336_, 1);
v_options_2341_ = lean_ctor_get(v___y_2336_, 2);
v_currRecDepth_2342_ = lean_ctor_get(v___y_2336_, 3);
v_maxRecDepth_2343_ = lean_ctor_get(v___y_2336_, 4);
v_ref_2344_ = lean_ctor_get(v___y_2336_, 5);
v_currNamespace_2345_ = lean_ctor_get(v___y_2336_, 6);
v_openDecls_2346_ = lean_ctor_get(v___y_2336_, 7);
v_initHeartbeats_2347_ = lean_ctor_get(v___y_2336_, 8);
v_maxHeartbeats_2348_ = lean_ctor_get(v___y_2336_, 9);
v_quotContext_2349_ = lean_ctor_get(v___y_2336_, 10);
v_currMacroScope_2350_ = lean_ctor_get(v___y_2336_, 11);
v_diag_2351_ = lean_ctor_get_uint8(v___y_2336_, sizeof(void*)*14);
v_cancelTk_x3f_2352_ = lean_ctor_get(v___y_2336_, 12);
v_suppressElabErrors_2353_ = lean_ctor_get_uint8(v___y_2336_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2354_ = lean_ctor_get(v___y_2336_, 13);
v_ref_2355_ = l_Lean_replaceRef(v_ref_2332_, v_ref_2344_);
lean_inc_ref(v_inheritedTraceOptions_2354_);
lean_inc(v_cancelTk_x3f_2352_);
lean_inc(v_currMacroScope_2350_);
lean_inc(v_quotContext_2349_);
lean_inc(v_maxHeartbeats_2348_);
lean_inc(v_initHeartbeats_2347_);
lean_inc(v_openDecls_2346_);
lean_inc(v_currNamespace_2345_);
lean_inc(v_maxRecDepth_2343_);
lean_inc(v_currRecDepth_2342_);
lean_inc_ref(v_options_2341_);
lean_inc_ref(v_fileMap_2340_);
lean_inc_ref(v_fileName_2339_);
v___x_2356_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2356_, 0, v_fileName_2339_);
lean_ctor_set(v___x_2356_, 1, v_fileMap_2340_);
lean_ctor_set(v___x_2356_, 2, v_options_2341_);
lean_ctor_set(v___x_2356_, 3, v_currRecDepth_2342_);
lean_ctor_set(v___x_2356_, 4, v_maxRecDepth_2343_);
lean_ctor_set(v___x_2356_, 5, v_ref_2355_);
lean_ctor_set(v___x_2356_, 6, v_currNamespace_2345_);
lean_ctor_set(v___x_2356_, 7, v_openDecls_2346_);
lean_ctor_set(v___x_2356_, 8, v_initHeartbeats_2347_);
lean_ctor_set(v___x_2356_, 9, v_maxHeartbeats_2348_);
lean_ctor_set(v___x_2356_, 10, v_quotContext_2349_);
lean_ctor_set(v___x_2356_, 11, v_currMacroScope_2350_);
lean_ctor_set(v___x_2356_, 12, v_cancelTk_x3f_2352_);
lean_ctor_set(v___x_2356_, 13, v_inheritedTraceOptions_2354_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*14, v_diag_2351_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*14 + 1, v_suppressElabErrors_2353_);
v___x_2357_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v_msg_2333_, v___y_2334_, v___y_2335_, v___x_2356_, v___y_2337_);
lean_dec_ref_known(v___x_2356_, 14);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_2358_, lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2358_, v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v_ref_2358_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_2366_, lean_object* v_msg_2367_, lean_object* v_declHint_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2376_; 
v___x_2374_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_2367_, v_declHint_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2366_, v_a_2375_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_2377_, lean_object* v_msg_2378_, lean_object* v_declHint_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2377_, v_msg_2378_, v_declHint_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v_ref_2377_);
return v_res_2385_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_2389_, lean_object* v_constName_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2396_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_2397_ = 0;
lean_inc(v_constName_2390_);
v___x_2398_ = l_Lean_MessageData_ofConstName(v_constName_2390_, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__1);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2389_, v___x_2401_, v_constName_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_2403_, lean_object* v_constName_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2403_, v_constName_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_ref_2403_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_ref_2417_; lean_object* v___x_2418_; 
v_ref_2417_ = lean_ctor_get(v___y_2414_, 5);
v___x_2418_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2417_, v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(lean_object* v_constName_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v_env_2433_; uint8_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = lean_st_ref_get(v___y_2430_);
v_env_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc_ref(v_env_2433_);
lean_dec(v___x_2432_);
v___x_2434_ = 0;
lean_inc(v_constName_2426_);
v___x_2435_ = l_Lean_Environment_findConstVal_x3f(v_env_2433_, v_constName_2426_, v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_constName_2426_);
v_val_2437_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2435_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_val_2437_);
lean_dec(v___x_2435_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 0);
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_val_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1___boxed(lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(lean_object* v_constName_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_env_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; 
v___x_2458_ = lean_st_ref_get(v___y_2456_);
v_env_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc_ref(v_env_2459_);
lean_dec(v___x_2458_);
v___x_2460_ = 0;
lean_inc(v_constName_2452_);
v___x_2461_ = l_Lean_Environment_find_x3f(v_env_2459_, v_constName_2452_, v___x_2460_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
return v___x_2462_;
}
else
{
lean_object* v_val_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_constName_2452_);
v_val_2463_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2461_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_val_2463_);
lean_dec(v___x_2461_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 0);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_val_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0___boxed(lean_object* v_constName_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_constName_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__4));
v___x_2485_ = lean_unsigned_to_nat(58u);
v___x_2486_ = lean_unsigned_to_nat(81u);
v___x_2487_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2489_ = l_mkPanicMessageWithDecl(v___x_2488_, v___x_2487_, v___x_2486_, v___x_2485_, v___x_2484_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2490_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_2491_ = lean_unsigned_to_nat(60u);
v___x_2492_ = lean_unsigned_to_nat(74u);
v___x_2493_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__3));
v___x_2494_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_2495_ = l_mkPanicMessageWithDecl(v___x_2494_, v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(lean_object* v_indName_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v_declName_2502_; lean_object* v___x_2503_; 
lean_inc_n(v_indName_2496_, 2);
v_declName_2502_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName(v_indName_2496_);
v___x_2503_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_indName_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
if (lean_obj_tag(v_a_2504_) == 5)
{
lean_object* v_val_2505_; lean_object* v_options_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v_a_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___y_2514_; uint8_t v___y_2661_; uint8_t v___x_2663_; 
v_val_2505_ = lean_ctor_get(v_a_2504_, 0);
lean_inc_ref(v_val_2505_);
lean_dec_ref_known(v_a_2504_, 1);
v_options_2506_ = lean_ctor_get(v_a_2499_, 2);
lean_inc(v_indName_2496_);
v___x_2507_ = l_Lean_mkCtorElimName(v_indName_2496_);
v___x_2508_ = 1;
v___x_2509_ = l_Lean_hasConst___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__1___redArg(v___x_2507_, v___x_2508_, v_a_2500_);
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = lean_unsigned_to_nat(2u);
v___x_2512_ = l_Lean_InductiveVal_numCtors(v_val_2505_);
v___x_2663_ = lean_nat_dec_lt(v___x_2511_, v___x_2512_);
if (v___x_2663_ == 0)
{
v___y_2661_ = v___x_2663_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2664_; uint8_t v___x_2665_; 
v___x_2664_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_backward_linearNoConfusionType;
v___x_2665_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_2506_, v___x_2664_);
v___y_2661_ = v___x_2665_;
goto v___jp_2660_;
}
v___jp_2513_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_inc(v_indName_2496_);
v___x_2515_ = l_Lean_mkCasesOnName(v_indName_2496_);
lean_inc(v___x_2515_);
v___x_2516_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__1(v___x_2515_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v_levelParams_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v_levelParams_2518_ = lean_ctor_get(v_a_2517_, 1);
lean_inc_n(v_levelParams_2518_, 2);
lean_dec(v_a_2517_);
v___x_2519_ = lean_box(0);
v___x_2520_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_2518_, v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 1)
{
lean_object* v_head_2521_; lean_object* v_tail_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2649_; 
v_head_2521_ = lean_ctor_get(v___x_2520_, 0);
v_tail_2522_ = lean_ctor_get(v___x_2520_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2524_ = v___x_2520_;
v_isShared_2525_ = v_isSharedCheck_2649_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_tail_2522_);
lean_inc(v_head_2521_);
lean_dec(v___x_2520_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2649_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_inc(v_head_2521_);
v___x_2526_ = l_Lean_Level_succ___override(v_head_2521_);
lean_inc(v_tail_2522_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_tail_2522_);
v___x_2528_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_inc_ref(v___x_2528_);
v___x_2529_ = l_Lean_mkConst(v___x_2515_, v___x_2528_);
lean_inc(v_a_2500_);
lean_inc_ref(v_a_2499_);
lean_inc(v_a_2498_);
lean_inc_ref(v_a_2497_);
lean_inc_ref(v___x_2529_);
v___x_2530_ = lean_infer_type(v___x_2529_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l_Lean_mkSort(v_head_2521_);
v___x_2533_ = lean_box(v___x_2508_);
lean_inc_ref_n(v___x_2532_, 2);
v___f_2534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2534_, 0, v___x_2532_);
lean_closure_set(v___f_2534_, 1, v___x_2533_);
v___x_2535_ = lean_box(v___y_2514_);
v___x_2536_ = lean_box(v___x_2508_);
v___f_2537_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___lam__7___boxed), 17, 11);
lean_closure_set(v___f_2537_, 0, v_val_2505_);
lean_closure_set(v___f_2537_, 1, v___x_2529_);
lean_closure_set(v___f_2537_, 2, v___f_2534_);
lean_closure_set(v___f_2537_, 3, v___x_2512_);
lean_closure_set(v___f_2537_, 4, v_indName_2496_);
lean_closure_set(v___f_2537_, 5, v___x_2528_);
lean_closure_set(v___f_2537_, 6, v___x_2535_);
lean_closure_set(v___f_2537_, 7, v_tail_2522_);
lean_closure_set(v___f_2537_, 8, v___x_2532_);
lean_closure_set(v___f_2537_, 9, v___x_2536_);
lean_closure_set(v___f_2537_, 10, v_a_2531_);
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_2539_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2538_, v___x_2532_, v___f_2537_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc_n(v_a_2540_, 2);
lean_dec_ref_known(v___x_2539_, 1);
lean_inc(v_a_2500_);
lean_inc_ref(v_a_2499_);
lean_inc(v_a_2498_);
lean_inc_ref(v_a_2497_);
v___x_2541_ = lean_infer_type(v_a_2540_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2623_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = lean_box(1);
lean_inc(v_declName_2502_);
v___x_2544_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v_declName_2502_, v_levelParams_2518_, v_a_2542_, v_a_2540_, v___x_2543_, v_a_2500_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2623_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2623_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set_tag(v___x_2547_, 1);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
uint8_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = 0;
v___x_2552_ = l_Lean_addDecl(v___x_2550_, v___x_2551_, v_a_2499_, v_a_2500_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2553_; lean_object* v_env_2554_; lean_object* v_nextMacroScope_2555_; lean_object* v_ngen_2556_; lean_object* v_auxDeclNGen_2557_; lean_object* v_traceState_2558_; lean_object* v_messages_2559_; lean_object* v_infoState_2560_; lean_object* v_snapshotTasks_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref_known(v___x_2552_, 1);
v___x_2553_ = lean_st_ref_take(v_a_2500_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
v_nextMacroScope_2555_ = lean_ctor_get(v___x_2553_, 1);
v_ngen_2556_ = lean_ctor_get(v___x_2553_, 2);
v_auxDeclNGen_2557_ = lean_ctor_get(v___x_2553_, 3);
v_traceState_2558_ = lean_ctor_get(v___x_2553_, 4);
v_messages_2559_ = lean_ctor_get(v___x_2553_, 6);
v_infoState_2560_ = lean_ctor_get(v___x_2553_, 7);
v_snapshotTasks_2561_ = lean_ctor_get(v___x_2553_, 8);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; 
v_unused_2621_ = lean_ctor_get(v___x_2553_, 5);
lean_dec(v_unused_2621_);
v___x_2563_ = v___x_2553_;
v_isShared_2564_ = v_isSharedCheck_2620_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_snapshotTasks_2561_);
lean_inc(v_infoState_2560_);
lean_inc(v_messages_2559_);
lean_inc(v_traceState_2558_);
lean_inc(v_auxDeclNGen_2557_);
lean_inc(v_ngen_2556_);
lean_inc(v_nextMacroScope_2555_);
lean_inc(v_env_2554_);
lean_dec(v___x_2553_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2620_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
lean_inc(v_declName_2502_);
v___x_2565_ = l_Lean_Meta_addToCompletionBlackList(v_env_2554_, v_declName_2502_);
v___x_2566_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 5, v___x_2566_);
lean_ctor_set(v___x_2563_, 0, v___x_2565_);
v___x_2568_ = v___x_2563_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2565_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v_nextMacroScope_2555_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v_ngen_2556_);
lean_ctor_set(v_reuseFailAlloc_2619_, 3, v_auxDeclNGen_2557_);
lean_ctor_set(v_reuseFailAlloc_2619_, 4, v_traceState_2558_);
lean_ctor_set(v_reuseFailAlloc_2619_, 5, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2619_, 6, v_messages_2559_);
lean_ctor_set(v_reuseFailAlloc_2619_, 7, v_infoState_2560_);
lean_ctor_set(v_reuseFailAlloc_2619_, 8, v_snapshotTasks_2561_);
v___x_2568_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_mctx_2571_; lean_object* v_zetaDeltaFVarIds_2572_; lean_object* v_postponed_2573_; lean_object* v_diag_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2617_; 
v___x_2569_ = lean_st_ref_set(v_a_2500_, v___x_2568_);
v___x_2570_ = lean_st_ref_take(v_a_2498_);
v_mctx_2571_ = lean_ctor_get(v___x_2570_, 0);
v_zetaDeltaFVarIds_2572_ = lean_ctor_get(v___x_2570_, 2);
v_postponed_2573_ = lean_ctor_get(v___x_2570_, 3);
v_diag_2574_ = lean_ctor_get(v___x_2570_, 4);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2570_, 1);
lean_dec(v_unused_2618_);
v___x_2576_ = v___x_2570_;
v_isShared_2577_ = v_isSharedCheck_2617_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_diag_2574_);
lean_inc(v_postponed_2573_);
lean_inc(v_zetaDeltaFVarIds_2572_);
lean_inc(v_mctx_2571_);
lean_dec(v___x_2570_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2617_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 1, v___x_2578_);
v___x_2580_ = v___x_2576_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_mctx_2571_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_zetaDeltaFVarIds_2572_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_postponed_2573_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_diag_2574_);
v___x_2580_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v_env_2583_; lean_object* v_nextMacroScope_2584_; lean_object* v_ngen_2585_; lean_object* v_auxDeclNGen_2586_; lean_object* v_traceState_2587_; lean_object* v_messages_2588_; lean_object* v_infoState_2589_; lean_object* v_snapshotTasks_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2614_; 
v___x_2581_ = lean_st_ref_set(v_a_2498_, v___x_2580_);
v___x_2582_ = lean_st_ref_take(v_a_2500_);
v_env_2583_ = lean_ctor_get(v___x_2582_, 0);
v_nextMacroScope_2584_ = lean_ctor_get(v___x_2582_, 1);
v_ngen_2585_ = lean_ctor_get(v___x_2582_, 2);
v_auxDeclNGen_2586_ = lean_ctor_get(v___x_2582_, 3);
v_traceState_2587_ = lean_ctor_get(v___x_2582_, 4);
v_messages_2588_ = lean_ctor_get(v___x_2582_, 6);
v_infoState_2589_ = lean_ctor_get(v___x_2582_, 7);
v_snapshotTasks_2590_ = lean_ctor_get(v___x_2582_, 8);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v___x_2582_, 5);
lean_dec(v_unused_2615_);
v___x_2592_ = v___x_2582_;
v_isShared_2593_ = v_isSharedCheck_2614_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_snapshotTasks_2590_);
lean_inc(v_infoState_2589_);
lean_inc(v_messages_2588_);
lean_inc(v_traceState_2587_);
lean_inc(v_auxDeclNGen_2586_);
lean_inc(v_ngen_2585_);
lean_inc(v_nextMacroScope_2584_);
lean_inc(v_env_2583_);
lean_dec(v___x_2582_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2614_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
lean_inc(v_declName_2502_);
v___x_2594_ = l_Lean_addProtected(v_env_2583_, v_declName_2502_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 5, v___x_2566_);
lean_ctor_set(v___x_2592_, 0, v___x_2594_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_nextMacroScope_2584_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v_ngen_2585_);
lean_ctor_set(v_reuseFailAlloc_2613_, 3, v_auxDeclNGen_2586_);
lean_ctor_set(v_reuseFailAlloc_2613_, 4, v_traceState_2587_);
lean_ctor_set(v_reuseFailAlloc_2613_, 5, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2613_, 6, v_messages_2588_);
lean_ctor_set(v_reuseFailAlloc_2613_, 7, v_infoState_2589_);
lean_ctor_set(v_reuseFailAlloc_2613_, 8, v_snapshotTasks_2590_);
v___x_2596_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v_mctx_2599_; lean_object* v_zetaDeltaFVarIds_2600_; lean_object* v_postponed_2601_; lean_object* v_diag_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2611_; 
v___x_2597_ = lean_st_ref_set(v_a_2500_, v___x_2596_);
v___x_2598_ = lean_st_ref_take(v_a_2498_);
v_mctx_2599_ = lean_ctor_get(v___x_2598_, 0);
v_zetaDeltaFVarIds_2600_ = lean_ctor_get(v___x_2598_, 2);
v_postponed_2601_ = lean_ctor_get(v___x_2598_, 3);
v_diag_2602_ = lean_ctor_get(v___x_2598_, 4);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; 
v_unused_2612_ = lean_ctor_get(v___x_2598_, 1);
lean_dec(v_unused_2612_);
v___x_2604_ = v___x_2598_;
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_diag_2602_);
lean_inc(v_postponed_2601_);
lean_inc(v_zetaDeltaFVarIds_2600_);
lean_inc(v_mctx_2599_);
lean_dec(v___x_2598_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___x_2578_);
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_mctx_2599_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_zetaDeltaFVarIds_2600_);
lean_ctor_set(v_reuseFailAlloc_2610_, 3, v_postponed_2601_);
lean_ctor_set(v_reuseFailAlloc_2610_, 4, v_diag_2602_);
v___x_2607_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2608_ = lean_st_ref_set(v_a_2498_, v___x_2607_);
v___x_2609_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v_declName_2502_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2609_;
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
lean_dec(v_declName_2502_);
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_a_2540_);
lean_dec(v_levelParams_2518_);
lean_dec(v_declName_2502_);
v_a_2624_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2541_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2541_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_levelParams_2518_);
lean_dec(v_declName_2502_);
v_a_2632_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2539_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2539_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v___x_2529_);
lean_dec_ref(v___x_2528_);
lean_dec(v_tail_2522_);
lean_dec(v_head_2521_);
lean_dec(v_levelParams_2518_);
lean_dec(v___x_2512_);
lean_dec_ref(v_val_2505_);
lean_dec(v_declName_2502_);
lean_dec(v_indName_2496_);
v_a_2640_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2530_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2530_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec(v___x_2520_);
lean_dec(v_levelParams_2518_);
lean_dec(v___x_2515_);
lean_dec(v___x_2512_);
lean_dec_ref(v_val_2505_);
lean_dec(v_declName_2502_);
lean_dec(v_indName_2496_);
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__5);
v___x_2651_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2650_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2651_;
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_dec(v___x_2515_);
lean_dec(v___x_2512_);
lean_dec_ref(v_val_2505_);
lean_dec(v_declName_2502_);
lean_dec(v_indName_2496_);
v_a_2652_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2516_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2516_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
v___jp_2660_:
{
if (v___y_2661_ == 0)
{
lean_dec(v_a_2510_);
v___y_2514_ = v___y_2661_;
goto v___jp_2513_;
}
else
{
uint8_t v___x_2662_; 
v___x_2662_ = lean_unbox(v_a_2510_);
lean_dec(v_a_2510_);
v___y_2514_ = v___x_2662_;
goto v___jp_2513_;
}
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec(v_a_2504_);
lean_dec(v_declName_2502_);
lean_dec(v_indName_2496_);
v___x_2666_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__6);
v___x_2667_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_2666_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2667_;
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_declName_2502_);
lean_dec(v_indName_2496_);
v_a_2668_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2503_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2503_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___boxed(lean_object* v_indName_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_indName_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(lean_object* v_i_2683_, lean_object* v_P_2684_, lean_object* v___x_2685_, lean_object* v_xs1_2686_, lean_object* v_zs1_2687_, lean_object* v_xs2_2688_, lean_object* v_as_2689_, lean_object* v_i_2690_, lean_object* v_j_2691_, lean_object* v_inv_2692_, lean_object* v_bs_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___redArg(v_i_2683_, v_P_2684_, v___x_2685_, v_xs1_2686_, v_zs1_2687_, v_xs2_2688_, v_as_2689_, v_i_2690_, v_j_2691_, v_bs_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4___boxed(lean_object* v_i_2700_, lean_object* v_P_2701_, lean_object* v___x_2702_, lean_object* v_xs1_2703_, lean_object* v_zs1_2704_, lean_object* v_xs2_2705_, lean_object* v_as_2706_, lean_object* v_i_2707_, lean_object* v_j_2708_, lean_object* v_inv_2709_, lean_object* v_bs_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__4(v_i_2700_, v_P_2701_, v___x_2702_, v_xs1_2703_, v_zs1_2704_, v_xs2_2705_, v_as_2706_, v_i_2707_, v_j_2708_, v_inv_2709_, v_bs_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec_ref(v_as_2706_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(lean_object* v_val_2717_, lean_object* v_P_2718_, lean_object* v_xs1_2719_, lean_object* v_xs2_2720_, lean_object* v_indName_2721_, lean_object* v___x_2722_, lean_object* v___x_2723_, lean_object* v_ysx2_2724_, uint8_t v___y_2725_, lean_object* v___x_2726_, lean_object* v___x_2727_, lean_object* v_tail_2728_, lean_object* v___x_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_j_2732_, lean_object* v_inv_2733_, lean_object* v_bs_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___redArg(v_val_2717_, v_P_2718_, v_xs1_2719_, v_xs2_2720_, v_indName_2721_, v___x_2722_, v___x_2723_, v_ysx2_2724_, v___y_2725_, v___x_2726_, v___x_2727_, v_tail_2728_, v___x_2729_, v_as_2730_, v_i_2731_, v_j_2732_, v_bs_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5___boxed(lean_object** _args){
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
lean_object* v_i_2755_ = _args[14];
lean_object* v_j_2756_ = _args[15];
lean_object* v_inv_2757_ = _args[16];
lean_object* v_bs_2758_ = _args[17];
lean_object* v___y_2759_ = _args[18];
lean_object* v___y_2760_ = _args[19];
lean_object* v___y_2761_ = _args[20];
lean_object* v___y_2762_ = _args[21];
lean_object* v___y_2763_ = _args[22];
_start:
{
uint8_t v___y_18947__boxed_2764_; lean_object* v_res_2765_; 
v___y_18947__boxed_2764_ = lean_unbox(v___y_2749_);
v_res_2765_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__5(v_val_2741_, v_P_2742_, v_xs1_2743_, v_xs2_2744_, v_indName_2745_, v___x_2746_, v___x_2747_, v_ysx2_2748_, v___y_18947__boxed_2764_, v___x_2750_, v___x_2751_, v_tail_2752_, v___x_2753_, v_as_2754_, v_i_2755_, v_j_2756_, v_inv_2757_, v_bs_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v_as_2754_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(lean_object* v_declName_2766_, uint8_t v_s_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg(v_declName_2766_, v_s_2767_, v___y_2769_, v___y_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___boxed(lean_object* v_declName_2774_, lean_object* v_s_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v_s_boxed_2781_; lean_object* v_res_2782_; 
v_s_boxed_2781_ = lean_unbox(v_s_2775_);
v_res_2782_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8(v_declName_2774_, v_s_boxed_2781_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(lean_object* v_00_u03b1_2783_, lean_object* v_constName_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___redArg(v_constName_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_constName_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0(v_00_u03b1_2791_, v_constName_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_2799_, lean_object* v_ref_2800_, lean_object* v_constName_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___redArg(v_ref_2800_, v_constName_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_ref_2809_, lean_object* v_constName_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4(v_00_u03b1_2808_, v_ref_2809_, v_constName_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v_ref_2809_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_2817_, lean_object* v_ref_2818_, lean_object* v_msg_2819_, lean_object* v_declHint_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_2818_, v_msg_2819_, v_declHint_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_2827_, lean_object* v_ref_2828_, lean_object* v_msg_2829_, lean_object* v_declHint_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_2827_, v_ref_2828_, v_msg_2829_, v_declHint_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v_ref_2828_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_2837_, lean_object* v_declHint_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_2837_, v_declHint_2838_, v___y_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_2845_, lean_object* v_declHint_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_2845_, v_declHint_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_2853_, lean_object* v_ref_2854_, lean_object* v_msg_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_2854_, v_msg_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_2862_, lean_object* v_ref_2863_, lean_object* v_msg_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_2862_, v_ref_2863_, v_msg_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v_ref_2863_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_2871_, lean_object* v_xs_2872_, lean_object* v_k_2873_, lean_object* v_tail_2874_, lean_object* v_tail_2875_, lean_object* v_v_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(v_x_2871_, v_xs_2872_, v_k_2873_, v_tail_2874_, v_tail_2875_, v_v_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(lean_object* v_xs_2886_, lean_object* v_k_2887_, lean_object* v_x_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
if (lean_obj_tag(v_x_2888_) == 1)
{
if (lean_obj_tag(v_x_2889_) == 1)
{
lean_object* v_head_2896_; lean_object* v_tail_2897_; lean_object* v_head_2898_; lean_object* v_tail_2899_; lean_object* v___x_2900_; 
v_head_2896_ = lean_ctor_get(v_x_2888_, 0);
lean_inc(v_head_2896_);
v_tail_2897_ = lean_ctor_get(v_x_2888_, 1);
lean_inc(v_tail_2897_);
lean_dec_ref_known(v_x_2888_, 2);
v_head_2898_ = lean_ctor_get(v_x_2889_, 0);
lean_inc(v_head_2898_);
v_tail_2899_ = lean_ctor_get(v_x_2889_, 1);
lean_inc(v_tail_2899_);
lean_dec_ref_known(v_x_2889_, 2);
v___x_2900_ = l_Lean_Meta_mkEqHEq(v_head_2896_, v_head_2898_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
lean_inc_ref(v_xs_2886_);
lean_inc_ref(v_x_2890_);
v___f_2902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2902_, 0, v_x_2890_);
lean_closure_set(v___f_2902_, 1, v_xs_2886_);
lean_closure_set(v___f_2902_, 2, v_k_2887_);
lean_closure_set(v___f_2902_, 3, v_tail_2897_);
lean_closure_set(v___f_2902_, 4, v_tail_2899_);
v___x_2903_ = lean_unsigned_to_nat(1u);
v___x_2904_ = lean_array_get_size(v_xs_2886_);
lean_dec_ref(v_xs_2886_);
v___x_2905_ = lean_nat_dec_lt(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_dec_ref(v_x_2890_);
v___x_2906_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2907_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2906_, v_a_2901_, v___f_2902_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2908_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_2909_ = lean_array_get_size(v_x_2890_);
lean_dec_ref(v_x_2890_);
v___x_2910_ = lean_nat_add(v___x_2909_, v___x_2903_);
v___x_2911_ = lean_name_append_index_after(v___x_2908_, v___x_2910_);
v___x_2912_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_2911_, v_a_2901_, v___f_2902_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
return v___x_2912_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_tail_2899_);
lean_dec(v_tail_2897_);
lean_dec_ref(v_x_2890_);
lean_dec_ref(v_k_2887_);
lean_dec_ref(v_xs_2886_);
v_a_2913_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2900_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2900_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v___x_2921_; 
lean_dec_ref_known(v_x_2888_, 2);
lean_dec(v_x_2889_);
lean_dec_ref(v_xs_2886_);
lean_inc(v_a_2894_);
lean_inc_ref(v_a_2893_);
lean_inc(v_a_2892_);
lean_inc_ref(v_a_2891_);
v___x_2921_ = lean_apply_6(v_k_2887_, v_x_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, lean_box(0));
return v___x_2921_;
}
}
else
{
lean_object* v___x_2922_; 
lean_dec(v_x_2889_);
lean_dec(v_x_2888_);
lean_dec_ref(v_xs_2886_);
lean_inc(v_a_2894_);
lean_inc_ref(v_a_2893_);
lean_inc(v_a_2892_);
lean_inc_ref(v_a_2891_);
v___x_2922_ = lean_apply_6(v_k_2887_, v_x_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, lean_box(0));
return v___x_2922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___lam__0(lean_object* v_x_2923_, lean_object* v_xs_2924_, lean_object* v_k_2925_, lean_object* v_tail_2926_, lean_object* v_tail_2927_, lean_object* v_v_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = lean_array_push(v_x_2923_, v_v_2928_);
v___x_2935_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2924_, v_k_2925_, v_tail_2926_, v_tail_2927_, v___x_2934_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___boxed(lean_object* v_xs_2936_, lean_object* v_k_2937_, lean_object* v_x_2938_, lean_object* v_x_2939_, lean_object* v_x_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2936_, v_k_2937_, v_x_2938_, v_x_2939_, v_x_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(lean_object* v_00_u03b1_2947_, lean_object* v_xs_2948_, lean_object* v_k_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_, lean_object* v_x_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2948_, v_k_2949_, v_x_2950_, v_x_2951_, v_x_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_xs_2960_, lean_object* v_k_2961_, lean_object* v_x_2962_, lean_object* v_x_2963_, lean_object* v_x_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go(v_00_u03b1_2959_, v_xs_2960_, v_k_2961_, v_x_2962_, v_x_2963_, v_x_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
lean_dec(v_a_2968_);
lean_dec_ref(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec_ref(v_a_2965_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(lean_object* v_xs_2973_, lean_object* v_ys_2974_, lean_object* v_k_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_inc_ref(v_xs_2973_);
v___x_2981_ = lean_array_to_list(v_xs_2973_);
v___x_2982_ = lean_array_to_list(v_ys_2974_);
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_2984_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg(v_xs_2973_, v_k_2975_, v___x_2981_, v___x_2982_, v___x_2983_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___boxed(lean_object* v_xs_2985_, lean_object* v_ys_2986_, lean_object* v_k_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2985_, v_ys_2986_, v_k_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(lean_object* v_00_u03b1_2994_, lean_object* v_inst_2995_, lean_object* v_xs_2996_, lean_object* v_ys_2997_, lean_object* v_k_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg(v_xs_2996_, v_ys_2997_, v_k_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___boxed(lean_object* v_00_u03b1_3005_, lean_object* v_inst_3006_, lean_object* v_xs_3007_, lean_object* v_ys_3008_, lean_object* v_k_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope(v_00_u03b1_3005_, v_inst_3006_, v_xs_3007_, v_ys_3008_, v_k_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_inst_3006_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed(lean_object* v_x_3016_, lean_object* v_x_3017_, lean_object* v_xs_3018_, lean_object* v_k_3019_, lean_object* v_tail_3020_, lean_object* v_tail_3021_, lean_object* v_v_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(v_x_3016_, v_x_3017_, v_xs_3018_, v_k_3019_, v_tail_3020_, v_tail_3021_, v_v_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(lean_object* v_xs_3029_, lean_object* v_k_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_){
_start:
{
if (lean_obj_tag(v_x_3031_) == 1)
{
if (lean_obj_tag(v_x_3032_) == 1)
{
lean_object* v_head_3040_; lean_object* v_tail_3041_; lean_object* v_head_3042_; lean_object* v_tail_3043_; lean_object* v___x_3044_; 
v_head_3040_ = lean_ctor_get(v_x_3031_, 0);
lean_inc_n(v_head_3040_, 2);
v_tail_3041_ = lean_ctor_get(v_x_3031_, 1);
lean_inc(v_tail_3041_);
lean_dec_ref_known(v_x_3031_, 2);
v_head_3042_ = lean_ctor_get(v_x_3032_, 0);
lean_inc_n(v_head_3042_, 2);
v_tail_3043_ = lean_ctor_get(v_x_3032_, 1);
lean_inc(v_tail_3043_);
lean_dec_ref_known(v_x_3032_, 2);
v___x_3044_ = l_Lean_Meta_isExprDefEq(v_head_3040_, v_head_3042_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___f_3046_; uint8_t v___x_3068_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
lean_inc(v_tail_3043_);
lean_inc(v_tail_3041_);
lean_inc_ref(v_k_3030_);
lean_inc_ref(v_xs_3029_);
lean_inc_ref(v_x_3034_);
lean_inc_ref(v_x_3033_);
v___f_3046_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3046_, 0, v_x_3033_);
lean_closure_set(v___f_3046_, 1, v_x_3034_);
lean_closure_set(v___f_3046_, 2, v_xs_3029_);
lean_closure_set(v___f_3046_, 3, v_k_3030_);
lean_closure_set(v___f_3046_, 4, v_tail_3041_);
lean_closure_set(v___f_3046_, 5, v_tail_3043_);
v___x_3068_ = l_List_isEmpty___redArg(v_tail_3041_);
if (v___x_3068_ == 0)
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_unbox(v_a_3045_);
lean_dec(v_a_3045_);
if (v___x_3069_ == 0)
{
lean_dec(v_tail_3043_);
lean_dec(v_tail_3041_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_k_3030_);
goto v___jp_3047_;
}
else
{
lean_object* v___x_3070_; 
lean_dec_ref(v___f_3046_);
lean_dec(v_head_3042_);
v___x_3070_ = l_Lean_Meta_mkEqRefl(v_head_3040_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = lean_array_push(v_x_3034_, v_a_3071_);
v_x_3031_ = v_tail_3041_;
v_x_3032_ = v_tail_3043_;
v_x_3034_ = v___x_3072_;
goto _start;
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_tail_3043_);
lean_dec(v_tail_3041_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_k_3030_);
lean_dec_ref(v_xs_3029_);
v_a_3074_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3070_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3070_);
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
}
else
{
lean_dec(v_a_3045_);
lean_dec(v_tail_3043_);
lean_dec(v_tail_3041_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_k_3030_);
goto v___jp_3047_;
}
v___jp_3047_:
{
lean_object* v___x_3048_; 
v___x_3048_ = l_Lean_Meta_mkEqHEq(v_head_3040_, v_head_3042_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_array_get_size(v_xs_3029_);
lean_dec_ref(v_xs_3029_);
v___x_3052_ = lean_nat_dec_lt(v___x_3050_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec_ref(v_x_3034_);
v___x_3053_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3054_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3053_, v_a_3049_, v___f_3046_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3055_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope_go___redArg___closed__1));
v___x_3056_ = lean_array_get_size(v_x_3034_);
lean_dec_ref(v_x_3034_);
v___x_3057_ = lean_nat_add(v___x_3056_, v___x_3050_);
v___x_3058_ = lean_name_append_index_after(v___x_3055_, v___x_3057_);
v___x_3059_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_3058_, v_a_3049_, v___f_3046_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
return v___x_3059_;
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v___f_3046_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_xs_3029_);
v_a_3060_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3048_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3048_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_tail_3043_);
lean_dec(v_head_3042_);
lean_dec(v_tail_3041_);
lean_dec(v_head_3040_);
lean_dec_ref(v_x_3034_);
lean_dec_ref(v_x_3033_);
lean_dec_ref(v_k_3030_);
lean_dec_ref(v_xs_3029_);
v_a_3082_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3044_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3044_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v___x_3090_; 
lean_dec_ref_known(v_x_3031_, 2);
lean_dec(v_x_3032_);
lean_dec_ref(v_xs_3029_);
lean_inc(v_a_3038_);
lean_inc_ref(v_a_3037_);
lean_inc(v_a_3036_);
lean_inc_ref(v_a_3035_);
v___x_3090_ = lean_apply_7(v_k_3030_, v_x_3033_, v_x_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, lean_box(0));
return v___x_3090_;
}
}
else
{
lean_object* v___x_3091_; 
lean_dec(v_x_3032_);
lean_dec(v_x_3031_);
lean_dec_ref(v_xs_3029_);
lean_inc(v_a_3038_);
lean_inc_ref(v_a_3037_);
lean_inc(v_a_3036_);
lean_inc_ref(v_a_3035_);
v___x_3091_ = lean_apply_7(v_k_3030_, v_x_3033_, v_x_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, lean_box(0));
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___lam__0(lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v_xs_3094_, lean_object* v_k_3095_, lean_object* v_tail_3096_, lean_object* v_tail_3097_, lean_object* v_v_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_inc_ref(v_v_3098_);
v___x_3104_ = lean_array_push(v_x_3092_, v_v_3098_);
v___x_3105_ = lean_array_push(v_x_3093_, v_v_3098_);
v___x_3106_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3094_, v_k_3095_, v_tail_3096_, v_tail_3097_, v___x_3104_, v___x_3105_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg___boxed(lean_object* v_xs_3107_, lean_object* v_k_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v_x_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3107_, v_k_3108_, v_x_3109_, v_x_3110_, v_x_3111_, v_x_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
lean_dec(v_a_3114_);
lean_dec_ref(v_a_3113_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(lean_object* v_00_u03b1_3119_, lean_object* v_xs_3120_, lean_object* v_k_3121_, lean_object* v_x_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_, lean_object* v_x_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3120_, v_k_3121_, v_x_3122_, v_x_3123_, v_x_3124_, v_x_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_xs_3133_, lean_object* v_k_3134_, lean_object* v_x_3135_, lean_object* v_x_3136_, lean_object* v_x_3137_, lean_object* v_x_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go(v_00_u03b1_3132_, v_xs_3133_, v_k_3134_, v_x_3135_, v_x_3136_, v_x_3137_, v_x_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(lean_object* v_xs_3145_, lean_object* v_ys_3146_, lean_object* v_k_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_inc_ref(v_xs_3145_);
v___x_3153_ = lean_array_to_list(v_xs_3145_);
v___x_3154_ = lean_array_to_list(v_ys_3146_);
v___x_3155_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withEqTelescope___redArg___closed__0));
v___x_3156_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope_go___redArg(v_xs_3145_, v_k_3147_, v___x_3153_, v___x_3154_, v___x_3155_, v___x_3155_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg___boxed(lean_object* v_xs_3157_, lean_object* v_ys_3158_, lean_object* v_k_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3157_, v_ys_3158_, v_k_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(lean_object* v_00_u03b1_3166_, lean_object* v_inst_3167_, lean_object* v_xs_3168_, lean_object* v_ys_3169_, lean_object* v_k_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v_xs_3168_, v_ys_3169_, v_k_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___boxed(lean_object* v_00_u03b1_3177_, lean_object* v_inst_3178_, lean_object* v_xs_3179_, lean_object* v_ys_3180_, lean_object* v_k_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope(v_00_u03b1_3177_, v_inst_3178_, v_xs_3179_, v_ys_3180_, v_k_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
lean_dec(v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_inst_3178_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(lean_object* v_mvarId_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_3188_, v_x_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3195_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3195_);
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
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_a_3204_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3195_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3195_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg___boxed(lean_object* v_mvarId_3212_, lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3212_, v_x_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(lean_object* v_00_u03b1_3220_, lean_object* v_mvarId_3221_, lean_object* v_x_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_mvarId_3221_, v_x_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___boxed(lean_object* v_00_u03b1_3229_, lean_object* v_mvarId_3230_, lean_object* v_x_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1(v_00_u03b1_3229_, v_mvarId_3230_, v_x_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(lean_object* v_msg_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___f_3244_; lean_object* v___x_4536__overap_3245_; lean_object* v___x_3246_; 
v___f_3244_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8___closed__0));
v___x_4536__overap_3245_ = lean_panic_fn_borrowed(v___f_3244_, v_msg_3238_);
lean_inc(v___y_3242_);
lean_inc_ref(v___y_3241_);
lean_inc(v___y_3240_);
lean_inc_ref(v___y_3239_);
v___x_3246_ = lean_apply_5(v___x_4536__overap_3245_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, lean_box(0));
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2___boxed(lean_object* v_msg_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__2(v_msg_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(lean_object* v_e_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_Expr_hasMVar(v_e_3254_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_e_3254_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; lean_object* v_mctx_3260_; lean_object* v___x_3261_; lean_object* v_fst_3262_; lean_object* v_snd_3263_; lean_object* v___x_3264_; lean_object* v_cache_3265_; lean_object* v_zetaDeltaFVarIds_3266_; lean_object* v_postponed_3267_; lean_object* v_diag_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3277_; 
v___x_3259_ = lean_st_ref_get(v___y_3255_);
v_mctx_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_mctx_3260_);
lean_dec(v___x_3259_);
v___x_3261_ = l_Lean_instantiateMVarsCore(v_mctx_3260_, v_e_3254_);
v_fst_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_fst_3262_);
v_snd_3263_ = lean_ctor_get(v___x_3261_, 1);
lean_inc(v_snd_3263_);
lean_dec_ref(v___x_3261_);
v___x_3264_ = lean_st_ref_take(v___y_3255_);
v_cache_3265_ = lean_ctor_get(v___x_3264_, 1);
v_zetaDeltaFVarIds_3266_ = lean_ctor_get(v___x_3264_, 2);
v_postponed_3267_ = lean_ctor_get(v___x_3264_, 3);
v_diag_3268_ = lean_ctor_get(v___x_3264_, 4);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v___x_3264_, 0);
lean_dec(v_unused_3278_);
v___x_3270_ = v___x_3264_;
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_diag_3268_);
lean_inc(v_postponed_3267_);
lean_inc(v_zetaDeltaFVarIds_3266_);
lean_inc(v_cache_3265_);
lean_dec(v___x_3264_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3277_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v_snd_3263_);
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_snd_3263_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_cache_3265_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_zetaDeltaFVarIds_3266_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_postponed_3267_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_diag_3268_);
v___x_3273_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_st_ref_set(v___y_3255_, v___x_3273_);
v___x_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3275_, 0, v_fst_3262_);
return v___x_3275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg___boxed(lean_object* v_e_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3279_, v___y_3280_);
lean_dec(v___y_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(lean_object* v_e_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___redArg(v_e_3283_, v___y_3285_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5___boxed(lean_object* v_e_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__5(v_e_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(lean_object* v_cls_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_options_3306_; uint8_t v_hasTrace_3307_; 
v_options_3306_ = lean_ctor_get(v___y_3303_, 2);
v_hasTrace_3307_ = lean_ctor_get_uint8(v_options_3306_, sizeof(void*)*1);
if (v_hasTrace_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec(v_cls_3300_);
v___x_3308_ = lean_box(v_hasTrace_3307_);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
else
{
lean_object* v_inheritedTraceOptions_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_inheritedTraceOptions_3310_ = lean_ctor_get(v___y_3303_, 13);
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
v___x_3312_ = l_Lean_Name_append(v___x_3311_, v_cls_3300_);
v___x_3313_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3310_, v_options_3306_, v___x_3312_);
lean_dec(v___x_3312_);
v___x_3314_ = lean_box(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___boxed(lean_object* v_cls_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0(v_cls_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
return v_res_3322_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3323_; double v___x_3324_; 
v___x_3323_ = lean_unsigned_to_nat(0u);
v___x_3324_ = lean_float_of_nat(v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(lean_object* v_cls_3328_, lean_object* v_msg_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_ref_3335_; lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3381_; 
v_ref_3335_ = lean_ctor_get(v___y_3332_, 5);
v___x_3336_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3381_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3381_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v_traceState_3342_; lean_object* v_env_3343_; lean_object* v_nextMacroScope_3344_; lean_object* v_ngen_3345_; lean_object* v_auxDeclNGen_3346_; lean_object* v_cache_3347_; lean_object* v_messages_3348_; lean_object* v_infoState_3349_; lean_object* v_snapshotTasks_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3380_; 
v___x_3341_ = lean_st_ref_take(v___y_3333_);
v_traceState_3342_ = lean_ctor_get(v___x_3341_, 4);
v_env_3343_ = lean_ctor_get(v___x_3341_, 0);
v_nextMacroScope_3344_ = lean_ctor_get(v___x_3341_, 1);
v_ngen_3345_ = lean_ctor_get(v___x_3341_, 2);
v_auxDeclNGen_3346_ = lean_ctor_get(v___x_3341_, 3);
v_cache_3347_ = lean_ctor_get(v___x_3341_, 5);
v_messages_3348_ = lean_ctor_get(v___x_3341_, 6);
v_infoState_3349_ = lean_ctor_get(v___x_3341_, 7);
v_snapshotTasks_3350_ = lean_ctor_get(v___x_3341_, 8);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3352_ = v___x_3341_;
v_isShared_3353_ = v_isSharedCheck_3380_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snapshotTasks_3350_);
lean_inc(v_infoState_3349_);
lean_inc(v_messages_3348_);
lean_inc(v_cache_3347_);
lean_inc(v_traceState_3342_);
lean_inc(v_auxDeclNGen_3346_);
lean_inc(v_ngen_3345_);
lean_inc(v_nextMacroScope_3344_);
lean_inc(v_env_3343_);
lean_dec(v___x_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3380_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
uint64_t v_tid_3354_; lean_object* v_traces_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3379_; 
v_tid_3354_ = lean_ctor_get_uint64(v_traceState_3342_, sizeof(void*)*1);
v_traces_3355_ = lean_ctor_get(v_traceState_3342_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_traceState_3342_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3357_ = v_traceState_3342_;
v_isShared_3358_ = v_isSharedCheck_3379_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_traces_3355_);
lean_dec(v_traceState_3342_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3379_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; double v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
v___x_3361_ = 0;
v___x_3362_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_3363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3363_, 0, v_cls_3328_);
lean_ctor_set(v___x_3363_, 1, v___x_3359_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3, v___x_3360_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3 + 8, v___x_3360_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*3 + 16, v___x_3361_);
v___x_3364_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__2));
v___x_3365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v_a_3337_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
lean_inc(v_ref_3335_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_ref_3335_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_PersistentArray_push___redArg(v_traces_3355_, v___x_3366_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3369_ = v___x_3357_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3367_);
lean_ctor_set_uint64(v_reuseFailAlloc_3378_, sizeof(void*)*1, v_tid_3354_);
v___x_3369_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v___x_3369_);
v___x_3371_ = v___x_3352_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_env_3343_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_nextMacroScope_3344_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_ngen_3345_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_auxDeclNGen_3346_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3377_, 5, v_cache_3347_);
lean_ctor_set(v_reuseFailAlloc_3377_, 6, v_messages_3348_);
lean_ctor_set(v_reuseFailAlloc_3377_, 7, v_infoState_3349_);
lean_ctor_set(v_reuseFailAlloc_3377_, 8, v_snapshotTasks_3350_);
v___x_3371_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3372_ = lean_st_ref_set(v___y_3333_, v___x_3371_);
v___x_3373_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3373_);
v___x_3375_ = v___x_3339_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___boxed(lean_object* v_cls_3382_, lean_object* v_msg_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3382_, v_msg_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
return v_res_3389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__0));
v___x_3392_ = l_Lean_stringToMessageData(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__2));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__4));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(lean_object* v___f_3399_, lean_object* v___x_3400_, lean_object* v_fst_3401_, lean_object* v_cls_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; 
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3403_);
v___x_3408_ = lean_apply_5(v___f_3399_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, lean_box(0));
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3440_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3440_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3440_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_unbox(v_a_3409_);
lean_dec(v_a_3409_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_cls_3402_);
lean_dec(v_fst_3401_);
lean_dec_ref(v___x_3400_);
v___x_3414_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3414_);
v___x_3416_ = v___x_3411_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
else
{
lean_object* v___x_3418_; 
lean_del_object(v___x_3411_);
lean_inc(v___y_3406_);
lean_inc_ref(v___y_3405_);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3403_);
lean_inc_ref(v___x_3400_);
v___x_3418_ = lean_infer_type(v___x_3400_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___x_3420_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__1);
v___x_3421_ = l_Lean_MessageData_ofExpr(v___x_3400_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__3);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = l_Lean_MessageData_ofExpr(v_a_3419_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___closed__5);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_fst_3401_);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3402_, v___x_3430_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v___x_3431_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_cls_3402_);
lean_dec(v_fst_3401_);
lean_dec_ref(v___x_3400_);
v_a_3432_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3418_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3418_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v_cls_3402_);
lean_dec(v_fst_3401_);
lean_dec_ref(v___x_3400_);
v_a_3441_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3408_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3408_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
return v___x_3446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1___boxed(lean_object* v___f_3449_, lean_object* v___x_3450_, lean_object* v_fst_3451_, lean_object* v_cls_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__1(v___f_3449_, v___x_3450_, v_fst_3451_, v_cls_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
return v_res_3458_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__0));
v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(lean_object* v_cls_3462_, lean_object* v___x_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_options_3472_; uint8_t v_hasTrace_3473_; 
v_options_3472_ = lean_ctor_get(v___y_3466_, 2);
v_hasTrace_3473_ = lean_ctor_get_uint8(v_options_3472_, sizeof(void*)*1);
if (v_hasTrace_3473_ == 0)
{
lean_dec_ref(v___x_3463_);
lean_dec(v_cls_3462_);
goto v___jp_3469_;
}
else
{
lean_object* v_inheritedTraceOptions_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; uint8_t v___x_3477_; 
v_inheritedTraceOptions_3474_ = lean_ctor_get(v___y_3466_, 13);
v___x_3475_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__0___closed__1));
lean_inc(v_cls_3462_);
v___x_3476_ = l_Lean_Name_append(v___x_3475_, v_cls_3462_);
v___x_3477_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3474_, v_options_3472_, v___x_3476_);
lean_dec(v___x_3476_);
if (v___x_3477_ == 0)
{
lean_dec_ref(v___x_3463_);
lean_dec(v_cls_3462_);
goto v___jp_3469_;
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3478_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___closed__1);
v___x_3479_ = l_Lean_MessageData_ofExpr(v___x_3463_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0(v_cls_3462_, v___x_3480_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
return v___x_3481_;
}
}
v___jp_3469_:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed(lean_object* v_cls_3482_, lean_object* v___x_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0(v_cls_3482_, v___x_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(lean_object* v_as_3494_, size_t v_sz_3495_, size_t v_i_3496_, lean_object* v_b_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_usize_dec_lt(v_i_3496_, v_sz_3495_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_b_3497_);
return v___x_3504_;
}
else
{
lean_object* v_fst_3505_; lean_object* v_snd_3506_; lean_object* v_cls_3507_; lean_object* v_a_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; 
v_fst_3505_ = lean_ctor_get(v_b_3497_, 0);
lean_inc_n(v_fst_3505_, 2);
v_snd_3506_ = lean_ctor_get(v_b_3497_, 1);
lean_inc(v_snd_3506_);
lean_dec_ref(v_b_3497_);
v_cls_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v_a_3508_ = lean_array_uget_borrowed(v_as_3494_, v_i_3496_);
v___x_3509_ = l_Lean_Expr_fvarId_x21(v_a_3508_);
v___x_3510_ = l_Lean_Meta_FVarSubst_get(v_snd_3506_, v___x_3509_);
lean_inc_ref(v___x_3510_);
v___f_3511_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3511_, 0, v_cls_3507_);
lean_closure_set(v___f_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__1___redArg(v_fst_3505_, v___f_3511_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec_ref_known(v___x_3512_, 1);
v___x_3513_ = l_Lean_Expr_fvarId_x21(v___x_3510_);
lean_dec_ref(v___x_3510_);
v___x_3514_ = l_Lean_Meta_substEq(v_fst_3505_, v___x_3513_, v_snd_3506_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3527_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v_fst_3516_ = lean_ctor_get(v_a_3515_, 0);
v_snd_3517_ = lean_ctor_get(v_a_3515_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_a_3515_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3519_ = v_a_3515_;
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_a_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3527_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v_fst_3516_);
lean_ctor_set(v___x_3519_, 0, v_snd_3517_);
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_snd_3517_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_fst_3516_);
v___x_3522_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
size_t v___x_3523_; size_t v___x_3524_; 
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3496_, v___x_3523_);
v_i_3496_ = v___x_3524_;
v_b_3497_ = v___x_3522_;
goto _start;
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_a_3528_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3514_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3514_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec_ref(v___x_3510_);
lean_dec(v_snd_3506_);
lean_dec(v_fst_3505_);
v_a_3536_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3512_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3512_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___boxed(lean_object* v_as_3544_, lean_object* v_sz_3545_, lean_object* v_i_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
size_t v_sz_boxed_3553_; size_t v_i_boxed_3554_; lean_object* v_res_3555_; 
v_sz_boxed_3553_ = lean_unbox_usize(v_sz_3545_);
lean_dec(v_sz_3545_);
v_i_boxed_3554_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_res_3555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3(v_as_3544_, v_sz_boxed_3553_, v_i_boxed_3554_, v_b_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v_as_3544_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_x_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v_ks_3560_; lean_object* v_vs_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3585_; 
v_ks_3560_ = lean_ctor_get(v_x_3556_, 0);
v_vs_3561_ = lean_ctor_get(v_x_3556_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_x_3556_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3563_ = v_x_3556_;
v_isShared_3564_ = v_isSharedCheck_3585_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_vs_3561_);
lean_inc(v_ks_3560_);
lean_dec(v_x_3556_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3585_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = lean_array_get_size(v_ks_3560_);
v___x_3566_ = lean_nat_dec_lt(v_x_3557_, v___x_3565_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3570_; 
lean_dec(v_x_3557_);
v___x_3567_ = lean_array_push(v_ks_3560_, v_x_3558_);
v___x_3568_ = lean_array_push(v_vs_3561_, v_x_3559_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3568_);
lean_ctor_set(v___x_3563_, 0, v___x_3567_);
v___x_3570_ = v___x_3563_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3567_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
else
{
lean_object* v_k_x27_3572_; uint8_t v___x_3573_; 
v_k_x27_3572_ = lean_array_fget_borrowed(v_ks_3560_, v_x_3557_);
v___x_3573_ = l_Lean_instBEqMVarId_beq(v_x_3558_, v_k_x27_3572_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3575_; 
if (v_isShared_3564_ == 0)
{
v___x_3575_ = v___x_3563_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_ks_3560_);
lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_vs_3561_);
v___x_3575_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = lean_unsigned_to_nat(1u);
v___x_3577_ = lean_nat_add(v_x_3557_, v___x_3576_);
lean_dec(v_x_3557_);
v_x_3556_ = v___x_3575_;
v_x_3557_ = v___x_3577_;
goto _start;
}
}
else
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3580_ = lean_array_fset(v_ks_3560_, v_x_3557_, v_x_3558_);
v___x_3581_ = lean_array_fset(v_vs_3561_, v_x_3557_, v_x_3559_);
lean_dec(v_x_3557_);
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3581_);
lean_ctor_set(v___x_3563_, 0, v___x_3580_);
v___x_3583_ = v___x_3563_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(lean_object* v_n_3586_, lean_object* v_k_3587_, lean_object* v_v_3588_){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_unsigned_to_nat(0u);
v___x_3590_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8_spec__9___redArg(v_n_3586_, v___x_3589_, v_k_3587_, v_v_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(lean_object* v_x_3592_, size_t v_x_3593_, size_t v_x_3594_, lean_object* v_x_3595_, lean_object* v_x_3596_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v_es_3597_; size_t v___x_3598_; size_t v___x_3599_; lean_object* v_j_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_es_3597_ = lean_ctor_get(v_x_3592_, 0);
v___x_3598_ = ((size_t)31ULL);
v___x_3599_ = lean_usize_land(v_x_3593_, v___x_3598_);
v_j_3600_ = lean_usize_to_nat(v___x_3599_);
v___x_3601_ = lean_array_get_size(v_es_3597_);
v___x_3602_ = lean_nat_dec_lt(v_j_3600_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_dec(v_j_3600_);
lean_dec(v_x_3596_);
lean_dec(v_x_3595_);
return v_x_3592_;
}
else
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3641_; 
lean_inc_ref(v_es_3597_);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_x_3592_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; 
v_unused_3642_ = lean_ctor_get(v_x_3592_, 0);
lean_dec(v_unused_3642_);
v___x_3604_ = v_x_3592_;
v_isShared_3605_ = v_isSharedCheck_3641_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v_x_3592_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3641_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_v_3606_; lean_object* v___x_3607_; lean_object* v_xs_x27_3608_; lean_object* v___y_3610_; 
v_v_3606_ = lean_array_fget(v_es_3597_, v_j_3600_);
v___x_3607_ = lean_box(0);
v_xs_x27_3608_ = lean_array_fset(v_es_3597_, v_j_3600_, v___x_3607_);
switch(lean_obj_tag(v_v_3606_))
{
case 0:
{
lean_object* v_key_3615_; lean_object* v_val_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
v_key_3615_ = lean_ctor_get(v_v_3606_, 0);
v_val_3616_ = lean_ctor_get(v_v_3606_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_v_3606_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3618_ = v_v_3606_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_val_3616_);
lean_inc(v_key_3615_);
lean_dec(v_v_3606_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
uint8_t v___x_3620_; 
v___x_3620_ = l_Lean_instBEqMVarId_beq(v_x_3595_, v_key_3615_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_del_object(v___x_3618_);
v___x_3621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3615_, v_val_3616_, v_x_3595_, v_x_3596_);
v___x_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
v___y_3610_ = v___x_3622_;
goto v___jp_3609_;
}
else
{
lean_object* v___x_3624_; 
lean_dec(v_val_3616_);
lean_dec(v_key_3615_);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 1, v_x_3596_);
lean_ctor_set(v___x_3618_, 0, v_x_3595_);
v___x_3624_ = v___x_3618_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_x_3595_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_x_3596_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
v___y_3610_ = v___x_3624_;
goto v___jp_3609_;
}
}
}
}
case 1:
{
lean_object* v_node_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3639_; 
v_node_3627_ = lean_ctor_get(v_v_3606_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v_v_3606_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3629_ = v_v_3606_;
v_isShared_3630_ = v_isSharedCheck_3639_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_node_3627_);
lean_dec(v_v_3606_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3639_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
size_t v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; size_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v___x_3631_ = ((size_t)5ULL);
v___x_3632_ = lean_usize_shift_right(v_x_3593_, v___x_3631_);
v___x_3633_ = ((size_t)1ULL);
v___x_3634_ = lean_usize_add(v_x_3594_, v___x_3633_);
v___x_3635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_node_3627_, v___x_3632_, v___x_3634_, v_x_3595_, v_x_3596_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3635_);
v___x_3637_ = v___x_3629_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
v___y_3610_ = v___x_3637_;
goto v___jp_3609_;
}
}
}
default: 
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3640_, 0, v_x_3595_);
lean_ctor_set(v___x_3640_, 1, v_x_3596_);
v___y_3610_ = v___x_3640_;
goto v___jp_3609_;
}
}
v___jp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_array_fset(v_xs_x27_3608_, v_j_3600_, v___y_3610_);
lean_dec(v_j_3600_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3611_);
v___x_3613_ = v___x_3604_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
}
}
else
{
lean_object* v_ks_3643_; lean_object* v_vs_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3664_; 
v_ks_3643_ = lean_ctor_get(v_x_3592_, 0);
v_vs_3644_ = lean_ctor_get(v_x_3592_, 1);
v_isSharedCheck_3664_ = !lean_is_exclusive(v_x_3592_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3646_ = v_x_3592_;
v_isShared_3647_ = v_isSharedCheck_3664_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_vs_3644_);
lean_inc(v_ks_3643_);
lean_dec(v_x_3592_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3664_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_ks_3643_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_vs_3644_);
v___x_3649_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v_newNode_3650_; uint8_t v___y_3652_; size_t v___x_3658_; uint8_t v___x_3659_; 
v_newNode_3650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__8___redArg(v___x_3649_, v_x_3595_, v_x_3596_);
v___x_3658_ = ((size_t)7ULL);
v___x_3659_ = lean_usize_dec_le(v___x_3658_, v_x_3594_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3660_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3650_);
v___x_3661_ = lean_unsigned_to_nat(4u);
v___x_3662_ = lean_nat_dec_lt(v___x_3660_, v___x_3661_);
lean_dec(v___x_3660_);
v___y_3652_ = v___x_3662_;
goto v___jp_3651_;
}
else
{
v___y_3652_ = v___x_3659_;
goto v___jp_3651_;
}
v___jp_3651_:
{
if (v___y_3652_ == 0)
{
lean_object* v_ks_3653_; lean_object* v_vs_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_ks_3653_ = lean_ctor_get(v_newNode_3650_, 0);
lean_inc_ref(v_ks_3653_);
v_vs_3654_ = lean_ctor_get(v_newNode_3650_, 1);
lean_inc_ref(v_vs_3654_);
lean_dec_ref(v_newNode_3650_);
v___x_3655_ = lean_unsigned_to_nat(0u);
v___x_3656_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___closed__0);
v___x_3657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_x_3594_, v_ks_3653_, v_vs_3654_, v___x_3655_, v___x_3656_);
lean_dec_ref(v_vs_3654_);
lean_dec_ref(v_ks_3653_);
return v___x_3657_;
}
else
{
return v_newNode_3650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(size_t v_depth_3665_, lean_object* v_keys_3666_, lean_object* v_vals_3667_, lean_object* v_i_3668_, lean_object* v_entries_3669_){
_start:
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3670_ = lean_array_get_size(v_keys_3666_);
v___x_3671_ = lean_nat_dec_lt(v_i_3668_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_dec(v_i_3668_);
return v_entries_3669_;
}
else
{
lean_object* v_k_3672_; lean_object* v_v_3673_; uint64_t v___x_3674_; size_t v_h_3675_; size_t v___x_3676_; lean_object* v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; size_t v___x_3680_; size_t v_h_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v_k_3672_ = lean_array_fget_borrowed(v_keys_3666_, v_i_3668_);
v_v_3673_ = lean_array_fget_borrowed(v_vals_3667_, v_i_3668_);
v___x_3674_ = l_Lean_instHashableMVarId_hash(v_k_3672_);
v_h_3675_ = lean_uint64_to_usize(v___x_3674_);
v___x_3676_ = ((size_t)5ULL);
v___x_3677_ = lean_unsigned_to_nat(1u);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_sub(v_depth_3665_, v___x_3678_);
v___x_3680_ = lean_usize_mul(v___x_3676_, v___x_3679_);
v_h_3681_ = lean_usize_shift_right(v_h_3675_, v___x_3680_);
v___x_3682_ = lean_nat_add(v_i_3668_, v___x_3677_);
lean_dec(v_i_3668_);
lean_inc(v_v_3673_);
lean_inc(v_k_3672_);
v___x_3683_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_entries_3669_, v_h_3681_, v_depth_3665_, v_k_3672_, v_v_3673_);
v_i_3668_ = v___x_3682_;
v_entries_3669_ = v___x_3683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg___boxed(lean_object* v_depth_3685_, lean_object* v_keys_3686_, lean_object* v_vals_3687_, lean_object* v_i_3688_, lean_object* v_entries_3689_){
_start:
{
size_t v_depth_boxed_3690_; lean_object* v_res_3691_; 
v_depth_boxed_3690_ = lean_unbox_usize(v_depth_3685_);
lean_dec(v_depth_3685_);
v_res_3691_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6_spec__9___redArg(v_depth_boxed_3690_, v_keys_3686_, v_vals_3687_, v_i_3688_, v_entries_3689_);
lean_dec_ref(v_vals_3687_);
lean_dec_ref(v_keys_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg___boxed(lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_, lean_object* v_x_3695_, lean_object* v_x_3696_){
_start:
{
size_t v_x_6491__boxed_3697_; size_t v_x_6492__boxed_3698_; lean_object* v_res_3699_; 
v_x_6491__boxed_3697_ = lean_unbox_usize(v_x_3693_);
lean_dec(v_x_3693_);
v_x_6492__boxed_3698_ = lean_unbox_usize(v_x_3694_);
lean_dec(v_x_3694_);
v_res_3699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3692_, v_x_6491__boxed_3697_, v_x_6492__boxed_3698_, v_x_3695_, v_x_3696_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
uint64_t v___x_3703_; size_t v___x_3704_; size_t v___x_3705_; lean_object* v___x_3706_; 
v___x_3703_ = l_Lean_instHashableMVarId_hash(v_x_3701_);
v___x_3704_ = lean_uint64_to_usize(v___x_3703_);
v___x_3705_ = ((size_t)1ULL);
v___x_3706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6___redArg(v_x_3700_, v___x_3704_, v___x_3705_, v_x_3701_, v_x_3702_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4___redArg(lean_object* v_mvarId_3707_, lean_object* v_val_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; lean_object* v_mctx_3712_; lean_object* v_cache_3713_; lean_object* v_zetaDeltaFVarIds_3714_; lean_object* v_postponed_3715_; lean_object* v_diag_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3744_; 
v___x_3711_ = lean_st_ref_take(v___y_3709_);
v_mctx_3712_ = lean_ctor_get(v___x_3711_, 0);
v_cache_3713_ = lean_ctor_get(v___x_3711_, 1);
v_zetaDeltaFVarIds_3714_ = lean_ctor_get(v___x_3711_, 2);
v_postponed_3715_ = lean_ctor_get(v___x_3711_, 3);
v_diag_3716_ = lean_ctor_get(v___x_3711_, 4);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3718_ = v___x_3711_;
v_isShared_3719_ = v_isSharedCheck_3744_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_diag_3716_);
lean_inc(v_postponed_3715_);
lean_inc(v_zetaDeltaFVarIds_3714_);
lean_inc(v_cache_3713_);
lean_inc(v_mctx_3712_);
lean_dec(v___x_3711_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3744_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v_depth_3720_; lean_object* v_levelAssignDepth_3721_; lean_object* v_lmvarCounter_3722_; lean_object* v_mvarCounter_3723_; lean_object* v_lDecls_3724_; lean_object* v_decls_3725_; lean_object* v_userNames_3726_; lean_object* v_lAssignment_3727_; lean_object* v_eAssignment_3728_; lean_object* v_dAssignment_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3743_; 
v_depth_3720_ = lean_ctor_get(v_mctx_3712_, 0);
v_levelAssignDepth_3721_ = lean_ctor_get(v_mctx_3712_, 1);
v_lmvarCounter_3722_ = lean_ctor_get(v_mctx_3712_, 2);
v_mvarCounter_3723_ = lean_ctor_get(v_mctx_3712_, 3);
v_lDecls_3724_ = lean_ctor_get(v_mctx_3712_, 4);
v_decls_3725_ = lean_ctor_get(v_mctx_3712_, 5);
v_userNames_3726_ = lean_ctor_get(v_mctx_3712_, 6);
v_lAssignment_3727_ = lean_ctor_get(v_mctx_3712_, 7);
v_eAssignment_3728_ = lean_ctor_get(v_mctx_3712_, 8);
v_dAssignment_3729_ = lean_ctor_get(v_mctx_3712_, 9);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_mctx_3712_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3731_ = v_mctx_3712_;
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_dAssignment_3729_);
lean_inc(v_eAssignment_3728_);
lean_inc(v_lAssignment_3727_);
lean_inc(v_userNames_3726_);
lean_inc(v_decls_3725_);
lean_inc(v_lDecls_3724_);
lean_inc(v_mvarCounter_3723_);
lean_inc(v_lmvarCounter_3722_);
lean_inc(v_levelAssignDepth_3721_);
lean_inc(v_depth_3720_);
lean_dec(v_mctx_3712_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3733_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4___redArg(v_eAssignment_3728_, v_mvarId_3707_, v_val_3708_);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 8, v___x_3733_);
v___x_3735_ = v___x_3731_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_depth_3720_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_levelAssignDepth_3721_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_lmvarCounter_3722_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_mvarCounter_3723_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_lDecls_3724_);
lean_ctor_set(v_reuseFailAlloc_3742_, 5, v_decls_3725_);
lean_ctor_set(v_reuseFailAlloc_3742_, 6, v_userNames_3726_);
lean_ctor_set(v_reuseFailAlloc_3742_, 7, v_lAssignment_3727_);
lean_ctor_set(v_reuseFailAlloc_3742_, 8, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3742_, 9, v_dAssignment_3729_);
v___x_3735_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3735_);
v___x_3737_ = v___x_3718_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_cache_3713_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_zetaDeltaFVarIds_3714_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_postponed_3715_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_diag_3716_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_st_ref_set(v___y_3709_, v___x_3737_);
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
uint8_t v___x_6706__boxed_3814_; lean_object* v_res_3815_; 
v___x_6706__boxed_3814_ = lean_unbox(v___x_3807_);
v_res_3815_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope___lam__2(v_motive_3802_, v_ys_3803_, v_e_3804_, v___f_3805_, v_cls_3806_, v___x_6706__boxed_3814_, v_eqs_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
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
size_t v_x_7015__boxed_3945_; size_t v_x_7016__boxed_3946_; lean_object* v_res_3947_; 
v_x_7015__boxed_3945_ = lean_unbox_usize(v_x_3941_);
lean_dec(v_x_3941_);
v_x_7016__boxed_3946_ = lean_unbox_usize(v_x_3942_);
lean_dec(v_x_3942_);
v_res_3947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__4_spec__4_spec__6(v_00_u03b2_3939_, v_x_3940_, v_x_7015__boxed_3945_, v_x_7016__boxed_3946_, v_x_3943_, v_x_3944_);
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
uint8_t v___x_11811__boxed_4093_; uint8_t v___x_11812__boxed_4094_; uint8_t v___x_11813__boxed_4095_; lean_object* v_res_4096_; 
v___x_11811__boxed_4093_ = lean_unbox(v___x_4084_);
v___x_11812__boxed_4094_ = lean_unbox(v___x_4085_);
v___x_11813__boxed_4095_ = lean_unbox(v___x_4086_);
v_res_4096_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__0(v___x_4081_, v_head_4082_, v_fs1_4083_, v___x_11811__boxed_4093_, v___x_11812__boxed_4094_, v___x_11813__boxed_4095_, v_k_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
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
uint8_t v___x_11887__boxed_4138_; uint8_t v___x_11888__boxed_4139_; uint8_t v___x_11889__boxed_4140_; lean_object* v_res_4141_; 
v___x_11887__boxed_4138_ = lean_unbox(v___x_4128_);
v___x_11888__boxed_4139_ = lean_unbox(v___x_4129_);
v___x_11889__boxed_4140_ = lean_unbox(v___x_4130_);
v_res_4141_ = l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1(v_head_4125_, v___x_4126_, v___x_4127_, v___x_11887__boxed_4138_, v___x_11888__boxed_4139_, v___x_11889__boxed_4140_, v_fs1_4131_, v_x_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
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
uint8_t v___x_12051__boxed_4266_; uint8_t v___x_12052__boxed_4267_; uint8_t v___x_12053__boxed_4268_; lean_object* v_res_4269_; 
v___x_12051__boxed_4266_ = lean_unbox(v___x_4247_);
v___x_12052__boxed_4267_ = lean_unbox(v___x_4248_);
v___x_12053__boxed_4268_ = lean_unbox(v___x_4249_);
v_res_4269_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___lam__0(v___x_4245_, v___x_4246_, v___x_12051__boxed_4266_, v___x_12052__boxed_4267_, v___x_12053__boxed_4268_, v___x_4250_, v___x_4251_, v_tail_4252_, v_ctors_4253_, v___x_4254_, v_xs2_4255_, v___x_4256_, v___x_4257_, v___x_4258_, v___x_4259_, v_xs1_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
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
v___x_4585_ = lean_st_ref_set(v___y_4527_, v___x_4584_);
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
v___x_4597_ = lean_st_ref_set(v___y_4525_, v___x_4596_);
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
v___x_4613_ = lean_st_ref_set(v___y_4527_, v___x_4612_);
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
v___x_4624_ = lean_st_ref_set(v___y_4525_, v___x_4623_);
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
lean_object* v_a_4765_; uint8_t v___y_4767_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4772_ = l_Lean_Expr_bindingDomain_x21(v_a_4762_);
lean_dec(v_a_4762_);
v___x_4773_ = l_Lean_Expr_isHEq(v___x_4772_);
lean_dec_ref(v___x_4772_);
if (v___x_4773_ == 0)
{
lean_dec(v_a_4765_);
v___y_4767_ = v___x_4773_;
goto v___jp_4766_;
}
else
{
uint8_t v___x_4774_; 
v___x_4774_ = l_Lean_Expr_isEq(v_a_4765_);
lean_dec(v_a_4765_);
v___y_4767_ = v___x_4774_;
goto v___jp_4766_;
}
v___jp_4766_:
{
if (v___y_4767_ == 0)
{
lean_object* v___x_4768_; 
lean_inc(v_a_4763_);
v___x_4768_ = l_Lean_Expr_app___override(v_b_4746_, v_a_4763_);
v_a_4753_ = v___x_4768_;
goto v___jp_4752_;
}
else
{
lean_object* v___x_4769_; 
lean_inc(v_a_4763_);
v___x_4769_ = l_Lean_Meta_mkHEqOfEq(v_a_4763_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4771_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
v___x_4771_ = l_Lean_Expr_app___override(v_b_4746_, v_a_4770_);
v_a_4753_ = v___x_4771_;
goto v___jp_4752_;
}
else
{
lean_dec_ref(v_b_4746_);
return v___x_4769_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1___boxed(lean_object* v_as_4775_, lean_object* v_sz_4776_, lean_object* v_i_4777_, lean_object* v_b_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
size_t v_sz_boxed_4784_; size_t v_i_boxed_4785_; lean_object* v_res_4786_; 
v_sz_boxed_4784_ = lean_unbox_usize(v_sz_4776_);
lean_dec(v_sz_4776_);
v_i_boxed_4785_ = lean_unbox_usize(v_i_4777_);
lean_dec(v_i_4777_);
v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(v_as_4775_, v_sz_boxed_4784_, v_i_boxed_4785_, v_b_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec_ref(v_as_4775_);
return v_res_4786_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__0));
v___x_4789_ = l_Lean_stringToMessageData(v___x_4788_);
return v___x_4789_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__2));
v___x_4792_ = l_Lean_stringToMessageData(v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(lean_object* v_range_4793_, lean_object* v_b_4794_, lean_object* v_i_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_stop_4801_; lean_object* v_step_4802_; lean_object* v_a_4804_; uint8_t v___x_4807_; 
v_stop_4801_ = lean_ctor_get(v_range_4793_, 1);
v_step_4802_ = lean_ctor_get(v_range_4793_, 2);
v___x_4807_ = lean_nat_dec_lt(v_i_4795_, v_stop_4801_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; 
lean_dec(v_i_4795_);
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v_b_4794_);
return v___x_4808_;
}
else
{
lean_object* v___x_4809_; 
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
lean_inc_ref(v_b_4794_);
v___x_4809_ = lean_infer_type(v_b_4794_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4811_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___x_4809_, 1);
v___x_4811_ = l_Lean_Meta_whnfForall(v_a_4810_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc(v_a_4812_);
lean_dec_ref_known(v___x_4811_, 1);
v___x_4813_ = l_Lean_Expr_bindingDomain_x21(v_a_4812_);
lean_dec(v_a_4812_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
v___x_4814_ = lean_whnf(v___x_4813_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4814_) == 0)
{
lean_object* v_a_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref_known(v___x_4814_, 1);
v___x_4816_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__0___closed__1));
v___x_4817_ = lean_unsigned_to_nat(4u);
v___x_4818_ = l_Lean_Expr_isAppOfArity(v_a_4815_, v___x_4816_, v___x_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4819_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__2));
v___x_4820_ = lean_unsigned_to_nat(3u);
v___x_4821_ = l_Lean_Expr_isAppOfArity(v_a_4815_, v___x_4819_, v___x_4820_);
if (v___x_4821_ == 0)
{
lean_object* v___x_4822_; 
lean_dec(v_i_4795_);
lean_inc(v___y_4799_);
lean_inc_ref(v___y_4798_);
lean_inc(v___y_4797_);
lean_inc_ref(v___y_4796_);
v___x_4822_ = lean_infer_type(v_b_4794_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v_a_4833_; lean_object* v___x_4835_; uint8_t v_isShared_4836_; uint8_t v_isSharedCheck_4840_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__1);
v___x_4825_ = l_Lean_MessageData_ofExpr(v_a_4815_);
v___x_4826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4824_);
lean_ctor_set(v___x_4826_, 1, v___x_4825_);
v___x_4827_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___closed__3);
v___x_4828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = lean_unsigned_to_nat(30u);
v___x_4830_ = l_Lean_inlineExpr(v_a_4823_, v___x_4829_);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4828_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_4831_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
v_a_4833_ = lean_ctor_get(v___x_4832_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4835_ = v___x_4832_;
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
else
{
lean_inc(v_a_4833_);
lean_dec(v___x_4832_);
v___x_4835_ = lean_box(0);
v_isShared_4836_ = v_isSharedCheck_4840_;
goto v_resetjp_4834_;
}
v_resetjp_4834_:
{
lean_object* v___x_4838_; 
if (v_isShared_4836_ == 0)
{
v___x_4838_ = v___x_4835_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_a_4833_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
else
{
lean_dec(v_a_4815_);
return v___x_4822_;
}
}
else
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = l_Lean_Expr_appFn_x21(v_a_4815_);
lean_dec(v_a_4815_);
v___x_4842_ = l_Lean_Expr_appArg_x21(v___x_4841_);
lean_dec_ref(v___x_4841_);
v___x_4843_ = l_Lean_Meta_mkEqRefl(v___x_4842_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4845_; 
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
lean_inc(v_a_4844_);
lean_dec_ref_known(v___x_4843_, 1);
v___x_4845_ = l_Lean_Expr_app___override(v_b_4794_, v_a_4844_);
v_a_4804_ = v___x_4845_;
goto v___jp_4803_;
}
else
{
lean_dec(v_i_4795_);
lean_dec_ref(v_b_4794_);
return v___x_4843_;
}
}
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4846_ = l_Lean_Expr_appFn_x21(v_a_4815_);
lean_dec(v_a_4815_);
v___x_4847_ = l_Lean_Expr_appFn_x21(v___x_4846_);
lean_dec_ref(v___x_4846_);
v___x_4848_ = l_Lean_Expr_appArg_x21(v___x_4847_);
lean_dec_ref(v___x_4847_);
v___x_4849_ = l_Lean_Meta_mkHEqRefl(v___x_4848_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
v___x_4851_ = l_Lean_Expr_app___override(v_b_4794_, v_a_4850_);
v_a_4804_ = v___x_4851_;
goto v___jp_4803_;
}
else
{
lean_dec(v_i_4795_);
lean_dec_ref(v_b_4794_);
return v___x_4849_;
}
}
}
else
{
lean_dec(v_i_4795_);
lean_dec_ref(v_b_4794_);
return v___x_4814_;
}
}
else
{
lean_dec(v_i_4795_);
lean_dec_ref(v_b_4794_);
return v___x_4811_;
}
}
else
{
lean_dec(v_i_4795_);
lean_dec_ref(v_b_4794_);
return v___x_4809_;
}
}
v___jp_4803_:
{
lean_object* v___x_4805_; 
v___x_4805_ = lean_nat_add(v_i_4795_, v_step_4802_);
lean_dec(v_i_4795_);
v_b_4794_ = v_a_4804_;
v_i_4795_ = v___x_4805_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg___boxed(lean_object* v_range_4852_, lean_object* v_b_4853_, lean_object* v_i_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v_range_4852_, v_b_4853_, v_i_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec_ref(v_range_4852_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0(lean_object* v___x_4861_, lean_object* v___x_4862_, lean_object* v___x_4863_, lean_object* v_xs_4864_, lean_object* v___x_4865_, lean_object* v___x_4866_, lean_object* v___x_4867_, lean_object* v___x_4868_, lean_object* v___x_4869_, lean_object* v___x_4870_, lean_object* v___x_4871_, lean_object* v_eqs_4872_, lean_object* v_P_4873_, lean_object* v___x_4874_, lean_object* v_eqvs_4875_, uint8_t v_a_4876_, uint8_t v___x_4877_, lean_object* v_head_4878_, lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v_numParams_4881_, lean_object* v_numFields_4882_, lean_object* v___x_4883_, lean_object* v___x_4884_, lean_object* v_k_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; 
v___x_4891_ = l_Lean_mkConst(v___x_4861_, v___x_4862_);
v___x_4892_ = l_Array_append___redArg(v___x_4863_, v_xs_4864_);
v___x_4893_ = l_Array_append___redArg(v___x_4892_, v___x_4865_);
lean_inc_ref_n(v___x_4866_, 2);
v___x_4894_ = lean_array_push(v___x_4866_, v___x_4867_);
v___x_4895_ = l_Array_append___redArg(v___x_4893_, v___x_4894_);
lean_dec_ref(v___x_4894_);
v___x_4896_ = l_Array_append___redArg(v___x_4895_, v_xs_4864_);
v___x_4897_ = l_Array_append___redArg(v___x_4896_, v___x_4868_);
v___x_4898_ = lean_array_push(v___x_4866_, v___x_4869_);
v___x_4899_ = l_Array_append___redArg(v___x_4897_, v___x_4898_);
lean_dec_ref(v___x_4898_);
v___x_4900_ = l_Lean_mkAppN(v___x_4891_, v___x_4899_);
lean_dec_ref(v___x_4899_);
v___x_4901_ = lean_array_get_size(v_xs_4864_);
lean_inc(v___x_4871_);
lean_inc(v___x_4870_);
v___x_4902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4870_);
lean_ctor_set(v___x_4902_, 1, v___x_4901_);
lean_ctor_set(v___x_4902_, 2, v___x_4871_);
v___x_4903_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v___x_4902_, v___x_4900_, v___x_4870_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
lean_dec_ref_known(v___x_4902_, 3);
if (lean_obj_tag(v___x_4903_) == 0)
{
lean_object* v_a_4904_; size_t v_sz_4905_; size_t v___x_4906_; lean_object* v___x_4907_; 
v_a_4904_ = lean_ctor_get(v___x_4903_, 0);
lean_inc(v_a_4904_);
lean_dec_ref_known(v___x_4903_, 1);
v_sz_4905_ = lean_array_size(v_eqs_4872_);
v___x_4906_ = ((size_t)0ULL);
v___x_4907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__1(v_eqs_4872_, v_sz_4905_, v___x_4906_, v_a_4904_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc(v_a_4908_);
lean_dec_ref_known(v___x_4907_, 1);
lean_inc_ref(v_k_4885_);
v___x_4909_ = l_Lean_Expr_app___override(v_a_4908_, v_k_4885_);
v___x_4910_ = l_Lean_Meta_mkExpectedTypeHint(v___x_4909_, v_P_4873_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; lean_object* v___x_4916_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = l_Array_append___redArg(v___x_4874_, v_eqvs_4875_);
v___x_4913_ = lean_array_push(v___x_4866_, v_k_4885_);
v___x_4914_ = l_Array_append___redArg(v___x_4912_, v___x_4913_);
lean_dec_ref(v___x_4913_);
v___x_4915_ = 1;
v___x_4916_ = l_Lean_Meta_mkLambdaFVars(v___x_4914_, v_a_4911_, v_a_4876_, v___x_4877_, v_a_4876_, v___x_4877_, v___x_4915_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
lean_dec_ref(v___x_4914_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v_a_4917_; lean_object* v___x_4918_; 
v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
lean_inc_n(v_a_4917_, 2);
lean_dec_ref_known(v___x_4916_, 1);
lean_inc(v___y_4889_);
lean_inc_ref(v___y_4888_);
lean_inc(v___y_4887_);
lean_inc_ref(v___y_4886_);
v___x_4918_ = lean_infer_type(v_a_4917_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
if (lean_obj_tag(v___x_4918_) == 0)
{
lean_object* v_a_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4983_; 
v_a_4919_ = lean_ctor_get(v___x_4918_, 0);
lean_inc(v_a_4919_);
lean_dec_ref_known(v___x_4918_, 1);
v___x_4920_ = l_Lean_Name_str___override(v_head_4878_, v___x_4879_);
v___x_4921_ = lean_box(1);
lean_inc(v___x_4920_);
v___x_4922_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__6___redArg(v___x_4920_, v___x_4880_, v_a_4919_, v_a_4917_, v___x_4921_, v___y_4889_);
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_4983_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4983_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
lean_ctor_set_tag(v___x_4925_, 1);
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
lean_object* v___x_4929_; 
v___x_4929_ = l_Lean_addDecl(v___x_4928_, v_a_4876_, v___y_4888_, v___y_4889_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v___x_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4980_; 
lean_dec_ref_known(v___x_4929_, 1);
lean_inc(v___x_4920_);
v___x_4930_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_4920_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4980_ == 0)
{
lean_object* v_unused_4981_; 
v_unused_4981_ = lean_ctor_get(v___x_4930_, 0);
lean_dec(v_unused_4981_);
v___x_4932_ = v___x_4930_;
v_isShared_4933_ = v_isSharedCheck_4980_;
goto v_resetjp_4931_;
}
else
{
lean_dec(v___x_4930_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4980_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v_env_4935_; lean_object* v_nextMacroScope_4936_; lean_object* v_ngen_4937_; lean_object* v_auxDeclNGen_4938_; lean_object* v_traceState_4939_; lean_object* v_messages_4940_; lean_object* v_infoState_4941_; lean_object* v_snapshotTasks_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4978_; 
v___x_4934_ = lean_st_ref_take(v___y_4889_);
v_env_4935_ = lean_ctor_get(v___x_4934_, 0);
v_nextMacroScope_4936_ = lean_ctor_get(v___x_4934_, 1);
v_ngen_4937_ = lean_ctor_get(v___x_4934_, 2);
v_auxDeclNGen_4938_ = lean_ctor_get(v___x_4934_, 3);
v_traceState_4939_ = lean_ctor_get(v___x_4934_, 4);
v_messages_4940_ = lean_ctor_get(v___x_4934_, 6);
v_infoState_4941_ = lean_ctor_get(v___x_4934_, 7);
v_snapshotTasks_4942_ = lean_ctor_get(v___x_4934_, 8);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4978_ == 0)
{
lean_object* v_unused_4979_; 
v_unused_4979_ = lean_ctor_get(v___x_4934_, 5);
lean_dec(v_unused_4979_);
v___x_4944_ = v___x_4934_;
v_isShared_4945_ = v_isSharedCheck_4978_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_snapshotTasks_4942_);
lean_inc(v_infoState_4941_);
lean_inc(v_messages_4940_);
lean_inc(v_traceState_4939_);
lean_inc(v_auxDeclNGen_4938_);
lean_inc(v_ngen_4937_);
lean_inc(v_nextMacroScope_4936_);
lean_inc(v_env_4935_);
lean_dec(v___x_4934_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4978_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4957_; 
v___x_4946_ = lean_nat_add(v_numParams_4881_, v___x_4871_);
lean_dec(v___x_4871_);
v___x_4947_ = lean_unsigned_to_nat(2u);
v___x_4948_ = lean_nat_mul(v___x_4947_, v_numFields_4882_);
v___x_4949_ = lean_nat_add(v___x_4946_, v___x_4948_);
lean_dec(v___x_4948_);
lean_dec(v___x_4946_);
v___x_4950_ = lean_array_get_size(v_eqvs_4875_);
v___x_4951_ = lean_nat_add(v___x_4949_, v___x_4950_);
lean_dec(v___x_4949_);
v___x_4952_ = l_Lean_Expr_getNumHeadForalls(v___x_4883_);
v___x_4953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4953_, 0, v___x_4951_);
lean_ctor_set(v___x_4953_, 1, v___x_4952_);
v___x_4954_ = l_Lean_markNoConfusion(v_env_4935_, v___x_4920_, v___x_4953_);
v___x_4955_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_4945_ == 0)
{
lean_ctor_set(v___x_4944_, 5, v___x_4955_);
lean_ctor_set(v___x_4944_, 0, v___x_4954_);
v___x_4957_ = v___x_4944_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4954_);
lean_ctor_set(v_reuseFailAlloc_4977_, 1, v_nextMacroScope_4936_);
lean_ctor_set(v_reuseFailAlloc_4977_, 2, v_ngen_4937_);
lean_ctor_set(v_reuseFailAlloc_4977_, 3, v_auxDeclNGen_4938_);
lean_ctor_set(v_reuseFailAlloc_4977_, 4, v_traceState_4939_);
lean_ctor_set(v_reuseFailAlloc_4977_, 5, v___x_4955_);
lean_ctor_set(v_reuseFailAlloc_4977_, 6, v_messages_4940_);
lean_ctor_set(v_reuseFailAlloc_4977_, 7, v_infoState_4941_);
lean_ctor_set(v_reuseFailAlloc_4977_, 8, v_snapshotTasks_4942_);
v___x_4957_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v_mctx_4960_; lean_object* v_zetaDeltaFVarIds_4961_; lean_object* v_postponed_4962_; lean_object* v_diag_4963_; lean_object* v___x_4965_; uint8_t v_isShared_4966_; uint8_t v_isSharedCheck_4975_; 
v___x_4958_ = lean_st_ref_set(v___y_4889_, v___x_4957_);
v___x_4959_ = lean_st_ref_take(v___y_4887_);
v_mctx_4960_ = lean_ctor_get(v___x_4959_, 0);
v_zetaDeltaFVarIds_4961_ = lean_ctor_get(v___x_4959_, 2);
v_postponed_4962_ = lean_ctor_get(v___x_4959_, 3);
v_diag_4963_ = lean_ctor_get(v___x_4959_, 4);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v___x_4959_, 1);
lean_dec(v_unused_4976_);
v___x_4965_ = v___x_4959_;
v_isShared_4966_ = v_isSharedCheck_4975_;
goto v_resetjp_4964_;
}
else
{
lean_inc(v_diag_4963_);
lean_inc(v_postponed_4962_);
lean_inc(v_zetaDeltaFVarIds_4961_);
lean_inc(v_mctx_4960_);
lean_dec(v___x_4959_);
v___x_4965_ = lean_box(0);
v_isShared_4966_ = v_isSharedCheck_4975_;
goto v_resetjp_4964_;
}
v_resetjp_4964_:
{
lean_object* v___x_4967_; lean_object* v___x_4969_; 
v___x_4967_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_4966_ == 0)
{
lean_ctor_set(v___x_4965_, 1, v___x_4967_);
v___x_4969_ = v___x_4965_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_mctx_4960_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4974_, 2, v_zetaDeltaFVarIds_4961_);
lean_ctor_set(v_reuseFailAlloc_4974_, 3, v_postponed_4962_);
lean_ctor_set(v_reuseFailAlloc_4974_, 4, v_diag_4963_);
v___x_4969_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
lean_object* v___x_4970_; lean_object* v___x_4972_; 
v___x_4970_ = lean_st_ref_set(v___y_4887_, v___x_4969_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4884_);
v___x_4972_ = v___x_4932_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4884_);
v___x_4972_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
return v___x_4972_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_4920_);
lean_dec(v___x_4871_);
return v___x_4929_;
}
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4991_; 
lean_dec(v_a_4917_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_head_4878_);
lean_dec(v___x_4871_);
v_a_4984_ = lean_ctor_get(v___x_4918_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4986_ = v___x_4918_;
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v___x_4918_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4991_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v___x_4989_; 
if (v_isShared_4987_ == 0)
{
v___x_4989_ = v___x_4986_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_a_4984_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_head_4878_);
lean_dec(v___x_4871_);
v_a_4992_ = lean_ctor_get(v___x_4916_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4916_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4916_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
lean_dec_ref(v_k_4885_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_head_4878_);
lean_dec_ref(v___x_4874_);
lean_dec(v___x_4871_);
lean_dec_ref(v___x_4866_);
v_a_5000_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4910_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4910_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
lean_dec_ref(v_k_4885_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_head_4878_);
lean_dec_ref(v___x_4874_);
lean_dec_ref(v_P_4873_);
lean_dec(v___x_4871_);
lean_dec_ref(v___x_4866_);
v_a_5008_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4907_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4907_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
return v___x_5013_;
}
}
}
}
else
{
lean_object* v_a_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5023_; 
lean_dec_ref(v_k_4885_);
lean_dec(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_head_4878_);
lean_dec_ref(v___x_4874_);
lean_dec_ref(v_P_4873_);
lean_dec(v___x_4871_);
lean_dec_ref(v___x_4866_);
v_a_5016_ = lean_ctor_get(v___x_4903_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_5023_ == 0)
{
v___x_5018_ = v___x_4903_;
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_a_5016_);
lean_dec(v___x_4903_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5023_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5021_; 
if (v_isShared_5019_ == 0)
{
v___x_5021_ = v___x_5018_;
goto v_reusejp_5020_;
}
else
{
lean_object* v_reuseFailAlloc_5022_; 
v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
v___x_5021_ = v_reuseFailAlloc_5022_;
goto v_reusejp_5020_;
}
v_reusejp_5020_:
{
return v___x_5021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_5024_ = _args[0];
lean_object* v___x_5025_ = _args[1];
lean_object* v___x_5026_ = _args[2];
lean_object* v_xs_5027_ = _args[3];
lean_object* v___x_5028_ = _args[4];
lean_object* v___x_5029_ = _args[5];
lean_object* v___x_5030_ = _args[6];
lean_object* v___x_5031_ = _args[7];
lean_object* v___x_5032_ = _args[8];
lean_object* v___x_5033_ = _args[9];
lean_object* v___x_5034_ = _args[10];
lean_object* v_eqs_5035_ = _args[11];
lean_object* v_P_5036_ = _args[12];
lean_object* v___x_5037_ = _args[13];
lean_object* v_eqvs_5038_ = _args[14];
lean_object* v_a_5039_ = _args[15];
lean_object* v___x_5040_ = _args[16];
lean_object* v_head_5041_ = _args[17];
lean_object* v___x_5042_ = _args[18];
lean_object* v___x_5043_ = _args[19];
lean_object* v_numParams_5044_ = _args[20];
lean_object* v_numFields_5045_ = _args[21];
lean_object* v___x_5046_ = _args[22];
lean_object* v___x_5047_ = _args[23];
lean_object* v_k_5048_ = _args[24];
lean_object* v___y_5049_ = _args[25];
lean_object* v___y_5050_ = _args[26];
lean_object* v___y_5051_ = _args[27];
lean_object* v___y_5052_ = _args[28];
lean_object* v___y_5053_ = _args[29];
_start:
{
uint8_t v_a_17756__boxed_5054_; uint8_t v___x_17757__boxed_5055_; lean_object* v_res_5056_; 
v_a_17756__boxed_5054_ = lean_unbox(v_a_5039_);
v___x_17757__boxed_5055_ = lean_unbox(v___x_5040_);
v_res_5056_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0(v___x_5024_, v___x_5025_, v___x_5026_, v_xs_5027_, v___x_5028_, v___x_5029_, v___x_5030_, v___x_5031_, v___x_5032_, v___x_5033_, v___x_5034_, v_eqs_5035_, v_P_5036_, v___x_5037_, v_eqvs_5038_, v_a_17756__boxed_5054_, v___x_17757__boxed_5055_, v_head_5041_, v___x_5042_, v___x_5043_, v_numParams_5044_, v_numFields_5045_, v___x_5046_, v___x_5047_, v_k_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec_ref(v___x_5046_);
lean_dec(v_numFields_5045_);
lean_dec(v_numParams_5044_);
lean_dec_ref(v_eqvs_5038_);
lean_dec_ref(v_eqs_5035_);
lean_dec_ref(v___x_5031_);
lean_dec_ref(v___x_5028_);
lean_dec_ref(v_xs_5027_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1(lean_object* v_head_5057_, lean_object* v_P_5058_, lean_object* v___x_5059_, lean_object* v_xs_5060_, lean_object* v_fields2_5061_, lean_object* v___x_5062_, lean_object* v___x_5063_, lean_object* v___x_5064_, lean_object* v___x_5065_, lean_object* v___x_5066_, lean_object* v___x_5067_, lean_object* v___x_5068_, lean_object* v___x_5069_, lean_object* v___x_5070_, lean_object* v___x_5071_, lean_object* v___x_5072_, uint8_t v_a_5073_, uint8_t v___x_5074_, lean_object* v___x_5075_, lean_object* v___x_5076_, lean_object* v_numParams_5077_, lean_object* v_numFields_5078_, lean_object* v___x_5079_, lean_object* v_eqvs_5080_, lean_object* v_eqs_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v___x_5087_; 
lean_inc_ref(v_P_5058_);
lean_inc(v_head_5057_);
v___x_5087_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg(v_head_5057_, v_P_5058_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
if (lean_obj_tag(v___x_5087_) == 0)
{
lean_object* v_a_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___f_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v_a_5088_ = lean_ctor_get(v___x_5087_, 0);
lean_inc(v_a_5088_);
lean_dec_ref_known(v___x_5087_, 1);
v___x_5089_ = l_Array_append___redArg(v___x_5059_, v_xs_5060_);
v___x_5090_ = l_Array_append___redArg(v___x_5089_, v_fields2_5061_);
v___x_5091_ = l_Lean_Expr_beta(v_a_5088_, v___x_5090_);
v___x_5092_ = lean_box(v_a_5073_);
v___x_5093_ = lean_box(v___x_5074_);
lean_inc_ref(v___x_5091_);
v___f_5094_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__0___boxed), 30, 24);
lean_closure_set(v___f_5094_, 0, v___x_5062_);
lean_closure_set(v___f_5094_, 1, v___x_5063_);
lean_closure_set(v___f_5094_, 2, v___x_5064_);
lean_closure_set(v___f_5094_, 3, v_xs_5060_);
lean_closure_set(v___f_5094_, 4, v___x_5065_);
lean_closure_set(v___f_5094_, 5, v___x_5066_);
lean_closure_set(v___f_5094_, 6, v___x_5067_);
lean_closure_set(v___f_5094_, 7, v___x_5068_);
lean_closure_set(v___f_5094_, 8, v___x_5069_);
lean_closure_set(v___f_5094_, 9, v___x_5070_);
lean_closure_set(v___f_5094_, 10, v___x_5071_);
lean_closure_set(v___f_5094_, 11, v_eqs_5081_);
lean_closure_set(v___f_5094_, 12, v_P_5058_);
lean_closure_set(v___f_5094_, 13, v___x_5072_);
lean_closure_set(v___f_5094_, 14, v_eqvs_5080_);
lean_closure_set(v___f_5094_, 15, v___x_5092_);
lean_closure_set(v___f_5094_, 16, v___x_5093_);
lean_closure_set(v___f_5094_, 17, v_head_5057_);
lean_closure_set(v___f_5094_, 18, v___x_5075_);
lean_closure_set(v___f_5094_, 19, v___x_5076_);
lean_closure_set(v___f_5094_, 20, v_numParams_5077_);
lean_closure_set(v___f_5094_, 21, v_numFields_5078_);
lean_closure_set(v___f_5094_, 22, v___x_5091_);
lean_closure_set(v___f_5094_, 23, v___x_5079_);
v___x_5095_ = ((lean_object*)(l_List_mapM_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__1___lam__1___closed__1));
v___x_5096_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5095_, v___x_5091_, v___f_5094_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_);
return v___x_5096_;
}
else
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5104_; 
lean_dec_ref(v_eqs_5081_);
lean_dec_ref(v_eqvs_5080_);
lean_dec(v_numFields_5078_);
lean_dec(v_numParams_5077_);
lean_dec(v___x_5076_);
lean_dec_ref(v___x_5075_);
lean_dec_ref(v___x_5072_);
lean_dec(v___x_5071_);
lean_dec(v___x_5070_);
lean_dec_ref(v___x_5069_);
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5067_);
lean_dec_ref(v___x_5066_);
lean_dec_ref(v___x_5065_);
lean_dec_ref(v___x_5064_);
lean_dec(v___x_5063_);
lean_dec(v___x_5062_);
lean_dec_ref(v_xs_5060_);
lean_dec_ref(v___x_5059_);
lean_dec_ref(v_P_5058_);
lean_dec(v_head_5057_);
v_a_5097_ = lean_ctor_get(v___x_5087_, 0);
v_isSharedCheck_5104_ = !lean_is_exclusive(v___x_5087_);
if (v_isSharedCheck_5104_ == 0)
{
v___x_5099_ = v___x_5087_;
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5087_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5104_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5102_; 
if (v_isShared_5100_ == 0)
{
v___x_5102_ = v___x_5099_;
goto v_reusejp_5101_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_a_5097_);
v___x_5102_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5101_;
}
v_reusejp_5101_:
{
return v___x_5102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_head_5105_ = _args[0];
lean_object* v_P_5106_ = _args[1];
lean_object* v___x_5107_ = _args[2];
lean_object* v_xs_5108_ = _args[3];
lean_object* v_fields2_5109_ = _args[4];
lean_object* v___x_5110_ = _args[5];
lean_object* v___x_5111_ = _args[6];
lean_object* v___x_5112_ = _args[7];
lean_object* v___x_5113_ = _args[8];
lean_object* v___x_5114_ = _args[9];
lean_object* v___x_5115_ = _args[10];
lean_object* v___x_5116_ = _args[11];
lean_object* v___x_5117_ = _args[12];
lean_object* v___x_5118_ = _args[13];
lean_object* v___x_5119_ = _args[14];
lean_object* v___x_5120_ = _args[15];
lean_object* v_a_5121_ = _args[16];
lean_object* v___x_5122_ = _args[17];
lean_object* v___x_5123_ = _args[18];
lean_object* v___x_5124_ = _args[19];
lean_object* v_numParams_5125_ = _args[20];
lean_object* v_numFields_5126_ = _args[21];
lean_object* v___x_5127_ = _args[22];
lean_object* v_eqvs_5128_ = _args[23];
lean_object* v_eqs_5129_ = _args[24];
lean_object* v___y_5130_ = _args[25];
lean_object* v___y_5131_ = _args[26];
lean_object* v___y_5132_ = _args[27];
lean_object* v___y_5133_ = _args[28];
lean_object* v___y_5134_ = _args[29];
_start:
{
uint8_t v_a_18077__boxed_5135_; uint8_t v___x_18078__boxed_5136_; lean_object* v_res_5137_; 
v_a_18077__boxed_5135_ = lean_unbox(v_a_5121_);
v___x_18078__boxed_5136_ = lean_unbox(v___x_5122_);
v_res_5137_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1(v_head_5105_, v_P_5106_, v___x_5107_, v_xs_5108_, v_fields2_5109_, v___x_5110_, v___x_5111_, v___x_5112_, v___x_5113_, v___x_5114_, v___x_5115_, v___x_5116_, v___x_5117_, v___x_5118_, v___x_5119_, v___x_5120_, v_a_18077__boxed_5135_, v___x_18078__boxed_5136_, v___x_5123_, v___x_5124_, v_numParams_5125_, v_numFields_5126_, v___x_5127_, v_eqvs_5128_, v_eqs_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_);
lean_dec(v___y_5133_);
lean_dec_ref(v___y_5132_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
lean_dec_ref(v_fields2_5109_);
return v_res_5137_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_5138_; lean_object* v_dummy_5139_; 
v___x_5138_ = lean_box(0);
v_dummy_5139_ = l_Lean_Expr_sort___override(v___x_5138_);
return v_dummy_5139_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2(lean_object* v___x_5140_, lean_object* v_val_5141_, lean_object* v___x_5142_, lean_object* v_head_5143_, lean_object* v_P_5144_, lean_object* v___x_5145_, lean_object* v_xs_5146_, lean_object* v_fields2_5147_, lean_object* v___x_5148_, lean_object* v___x_5149_, lean_object* v___x_5150_, lean_object* v___x_5151_, lean_object* v___x_5152_, lean_object* v___x_5153_, lean_object* v___x_5154_, uint8_t v_a_5155_, uint8_t v___x_5156_, lean_object* v___x_5157_, lean_object* v___x_5158_, lean_object* v_numParams_5159_, lean_object* v_numFields_5160_, lean_object* v___x_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_, lean_object* v___y_5165_){
_start:
{
lean_object* v___x_5167_; 
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
lean_inc_ref(v___x_5140_);
v___x_5167_ = lean_infer_type(v___x_5140_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5167_) == 0)
{
lean_object* v_a_5168_; lean_object* v___x_5169_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref_known(v___x_5167_, 1);
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
v___x_5169_ = lean_whnf(v_a_5168_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5169_) == 0)
{
lean_object* v_a_5170_; lean_object* v_numIndices_5171_; lean_object* v___x_5172_; 
v_a_5170_ = lean_ctor_get(v___x_5169_, 0);
lean_inc(v_a_5170_);
lean_dec_ref_known(v___x_5169_, 1);
v_numIndices_5171_ = lean_ctor_get(v_val_5141_, 2);
lean_inc(v_numIndices_5171_);
lean_dec_ref(v_val_5141_);
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
lean_inc_ref(v___x_5142_);
v___x_5172_ = lean_infer_type(v___x_5142_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5174_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc(v_a_5173_);
lean_dec_ref_known(v___x_5172_, 1);
lean_inc(v___y_5165_);
lean_inc_ref(v___y_5164_);
lean_inc(v___y_5163_);
lean_inc_ref(v___y_5162_);
v___x_5174_ = lean_whnf(v_a_5173_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
if (lean_obj_tag(v___x_5174_) == 0)
{
lean_object* v_a_5175_; lean_object* v_dummy_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___f_5182_; lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; 
v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
lean_inc(v_a_5175_);
lean_dec_ref_known(v___x_5174_, 1);
v_dummy_5176_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___closed__0);
lean_inc_n(v_numIndices_5171_, 2);
v___x_5177_ = lean_mk_array(v_numIndices_5171_, v_dummy_5176_);
lean_inc_ref(v___x_5177_);
v___x_5178_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5171_, v_a_5170_, v___x_5177_);
v___x_5179_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsN_loop(v_numIndices_5171_, v_a_5175_, v___x_5177_);
v___x_5180_ = lean_box(v_a_5155_);
v___x_5181_ = lean_box(v___x_5156_);
lean_inc_ref(v___x_5142_);
lean_inc_ref(v___x_5179_);
lean_inc_ref(v___x_5140_);
lean_inc_ref(v___x_5178_);
v___f_5182_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__1___boxed), 30, 23);
lean_closure_set(v___f_5182_, 0, v_head_5143_);
lean_closure_set(v___f_5182_, 1, v_P_5144_);
lean_closure_set(v___f_5182_, 2, v___x_5145_);
lean_closure_set(v___f_5182_, 3, v_xs_5146_);
lean_closure_set(v___f_5182_, 4, v_fields2_5147_);
lean_closure_set(v___f_5182_, 5, v___x_5148_);
lean_closure_set(v___f_5182_, 6, v___x_5149_);
lean_closure_set(v___f_5182_, 7, v___x_5150_);
lean_closure_set(v___f_5182_, 8, v___x_5178_);
lean_closure_set(v___f_5182_, 9, v___x_5151_);
lean_closure_set(v___f_5182_, 10, v___x_5140_);
lean_closure_set(v___f_5182_, 11, v___x_5179_);
lean_closure_set(v___f_5182_, 12, v___x_5142_);
lean_closure_set(v___f_5182_, 13, v___x_5152_);
lean_closure_set(v___f_5182_, 14, v___x_5153_);
lean_closure_set(v___f_5182_, 15, v___x_5154_);
lean_closure_set(v___f_5182_, 16, v___x_5180_);
lean_closure_set(v___f_5182_, 17, v___x_5181_);
lean_closure_set(v___f_5182_, 18, v___x_5157_);
lean_closure_set(v___f_5182_, 19, v___x_5158_);
lean_closure_set(v___f_5182_, 20, v_numParams_5159_);
lean_closure_set(v___f_5182_, 21, v_numFields_5160_);
lean_closure_set(v___f_5182_, 22, v___x_5161_);
v___x_5183_ = lean_array_push(v___x_5178_, v___x_5140_);
v___x_5184_ = lean_array_push(v___x_5179_, v___x_5142_);
v___x_5185_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_withNeededEqTelescope___redArg(v___x_5183_, v___x_5184_, v___f_5182_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
return v___x_5185_;
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
lean_dec(v_numIndices_5171_);
lean_dec(v_a_5170_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v_numFields_5160_);
lean_dec(v_numParams_5159_);
lean_dec(v___x_5158_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v___x_5154_);
lean_dec(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec_ref(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec_ref(v_fields2_5147_);
lean_dec_ref(v_xs_5146_);
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_P_5144_);
lean_dec(v_head_5143_);
lean_dec_ref(v___x_5142_);
lean_dec_ref(v___x_5140_);
v_a_5186_ = lean_ctor_get(v___x_5174_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5174_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5174_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5174_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec(v_numIndices_5171_);
lean_dec(v_a_5170_);
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v_numFields_5160_);
lean_dec(v_numParams_5159_);
lean_dec(v___x_5158_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v___x_5154_);
lean_dec(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec_ref(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec_ref(v_fields2_5147_);
lean_dec_ref(v_xs_5146_);
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_P_5144_);
lean_dec(v_head_5143_);
lean_dec_ref(v___x_5142_);
lean_dec_ref(v___x_5140_);
v_a_5194_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5172_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5172_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
else
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v_numFields_5160_);
lean_dec(v_numParams_5159_);
lean_dec(v___x_5158_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v___x_5154_);
lean_dec(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec_ref(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec_ref(v_fields2_5147_);
lean_dec_ref(v_xs_5146_);
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_P_5144_);
lean_dec(v_head_5143_);
lean_dec_ref(v___x_5142_);
lean_dec_ref(v_val_5141_);
lean_dec_ref(v___x_5140_);
v_a_5202_ = lean_ctor_get(v___x_5169_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5169_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5169_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5169_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v___x_5207_; 
if (v_isShared_5205_ == 0)
{
v___x_5207_ = v___x_5204_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_dec(v___y_5165_);
lean_dec_ref(v___y_5164_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v_numFields_5160_);
lean_dec(v_numParams_5159_);
lean_dec(v___x_5158_);
lean_dec_ref(v___x_5157_);
lean_dec_ref(v___x_5154_);
lean_dec(v___x_5153_);
lean_dec(v___x_5152_);
lean_dec_ref(v___x_5151_);
lean_dec_ref(v___x_5150_);
lean_dec(v___x_5149_);
lean_dec(v___x_5148_);
lean_dec_ref(v_fields2_5147_);
lean_dec_ref(v_xs_5146_);
lean_dec_ref(v___x_5145_);
lean_dec_ref(v_P_5144_);
lean_dec(v_head_5143_);
lean_dec_ref(v___x_5142_);
lean_dec_ref(v_val_5141_);
lean_dec_ref(v___x_5140_);
v_a_5210_ = lean_ctor_get(v___x_5167_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5167_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5167_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5167_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_5218_ = _args[0];
lean_object* v_val_5219_ = _args[1];
lean_object* v___x_5220_ = _args[2];
lean_object* v_head_5221_ = _args[3];
lean_object* v_P_5222_ = _args[4];
lean_object* v___x_5223_ = _args[5];
lean_object* v_xs_5224_ = _args[6];
lean_object* v_fields2_5225_ = _args[7];
lean_object* v___x_5226_ = _args[8];
lean_object* v___x_5227_ = _args[9];
lean_object* v___x_5228_ = _args[10];
lean_object* v___x_5229_ = _args[11];
lean_object* v___x_5230_ = _args[12];
lean_object* v___x_5231_ = _args[13];
lean_object* v___x_5232_ = _args[14];
lean_object* v_a_5233_ = _args[15];
lean_object* v___x_5234_ = _args[16];
lean_object* v___x_5235_ = _args[17];
lean_object* v___x_5236_ = _args[18];
lean_object* v_numParams_5237_ = _args[19];
lean_object* v_numFields_5238_ = _args[20];
lean_object* v___x_5239_ = _args[21];
lean_object* v___y_5240_ = _args[22];
lean_object* v___y_5241_ = _args[23];
lean_object* v___y_5242_ = _args[24];
lean_object* v___y_5243_ = _args[25];
lean_object* v___y_5244_ = _args[26];
_start:
{
uint8_t v_a_18184__boxed_5245_; uint8_t v___x_18185__boxed_5246_; lean_object* v_res_5247_; 
v_a_18184__boxed_5245_ = lean_unbox(v_a_5233_);
v___x_18185__boxed_5246_ = lean_unbox(v___x_5234_);
v_res_5247_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2(v___x_5218_, v_val_5219_, v___x_5220_, v_head_5221_, v_P_5222_, v___x_5223_, v_xs_5224_, v_fields2_5225_, v___x_5226_, v___x_5227_, v___x_5228_, v___x_5229_, v___x_5230_, v___x_5231_, v___x_5232_, v_a_18184__boxed_5245_, v___x_18185__boxed_5246_, v___x_5235_, v___x_5236_, v_numParams_5237_, v_numFields_5238_, v___x_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
return v_res_5247_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3(lean_object* v_P_5248_, lean_object* v_xs_5249_, lean_object* v_fields1_5250_, lean_object* v_head_5251_, lean_object* v_tail_5252_, lean_object* v_val_5253_, lean_object* v___x_5254_, lean_object* v___x_5255_, lean_object* v___x_5256_, uint8_t v_a_5257_, uint8_t v___x_5258_, lean_object* v___x_5259_, lean_object* v___x_5260_, lean_object* v_numParams_5261_, lean_object* v_numFields_5262_, lean_object* v___x_5263_, lean_object* v_fields2_5264_, lean_object* v_x_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_){
_start:
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
v___x_5271_ = lean_unsigned_to_nat(1u);
v___x_5272_ = lean_mk_empty_array_with_capacity(v___x_5271_);
lean_inc_ref(v_P_5248_);
lean_inc_ref(v___x_5272_);
v___x_5273_ = lean_array_push(v___x_5272_, v_P_5248_);
lean_inc_ref_n(v_xs_5249_, 3);
v___x_5274_ = l_Array_append___redArg(v_xs_5249_, v___x_5273_);
v___x_5275_ = l_Array_append___redArg(v___x_5274_, v_fields1_5250_);
v___x_5276_ = l_Array_append___redArg(v___x_5275_, v_fields2_5264_);
lean_inc(v_head_5251_);
v___x_5277_ = l_Lean_mkConst(v_head_5251_, v_tail_5252_);
v___x_5278_ = l_Array_append___redArg(v_xs_5249_, v_fields1_5250_);
lean_inc_ref(v___x_5277_);
v___x_5279_ = l_Lean_mkAppN(v___x_5277_, v___x_5278_);
v___x_5280_ = l_Array_append___redArg(v_xs_5249_, v_fields2_5264_);
v___x_5281_ = l_Lean_mkAppN(v___x_5277_, v___x_5280_);
lean_dec_ref(v___x_5280_);
v___x_5282_ = lean_box(v_a_5257_);
v___x_5283_ = lean_box(v___x_5258_);
lean_inc_ref(v___x_5276_);
lean_inc_ref(v_fields2_5264_);
v___f_5284_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__2___boxed), 27, 22);
lean_closure_set(v___f_5284_, 0, v___x_5279_);
lean_closure_set(v___f_5284_, 1, v_val_5253_);
lean_closure_set(v___f_5284_, 2, v___x_5281_);
lean_closure_set(v___f_5284_, 3, v_head_5251_);
lean_closure_set(v___f_5284_, 4, v_P_5248_);
lean_closure_set(v___f_5284_, 5, v___x_5278_);
lean_closure_set(v___f_5284_, 6, v_xs_5249_);
lean_closure_set(v___f_5284_, 7, v_fields2_5264_);
lean_closure_set(v___f_5284_, 8, v___x_5254_);
lean_closure_set(v___f_5284_, 9, v___x_5255_);
lean_closure_set(v___f_5284_, 10, v___x_5273_);
lean_closure_set(v___f_5284_, 11, v___x_5272_);
lean_closure_set(v___f_5284_, 12, v___x_5256_);
lean_closure_set(v___f_5284_, 13, v___x_5271_);
lean_closure_set(v___f_5284_, 14, v___x_5276_);
lean_closure_set(v___f_5284_, 15, v___x_5282_);
lean_closure_set(v___f_5284_, 16, v___x_5283_);
lean_closure_set(v___f_5284_, 17, v___x_5259_);
lean_closure_set(v___f_5284_, 18, v___x_5260_);
lean_closure_set(v___f_5284_, 19, v_numParams_5261_);
lean_closure_set(v___f_5284_, 20, v_numFields_5262_);
lean_closure_set(v___f_5284_, 21, v___x_5263_);
v___x_5285_ = lean_alloc_closure((void*)(l_Lean_Meta_withImplicitBinderInfos___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp_spec__2___boxed), 8, 3);
lean_closure_set(v___x_5285_, 0, lean_box(0));
lean_closure_set(v___x_5285_, 1, v___x_5276_);
lean_closure_set(v___x_5285_, 2, v___f_5284_);
v___x_5286_ = l_Lean_Meta_withPrimedNames___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__2___redArg(v_fields2_5264_, v___x_5285_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3___boxed(lean_object** _args){
lean_object* v_P_5287_ = _args[0];
lean_object* v_xs_5288_ = _args[1];
lean_object* v_fields1_5289_ = _args[2];
lean_object* v_head_5290_ = _args[3];
lean_object* v_tail_5291_ = _args[4];
lean_object* v_val_5292_ = _args[5];
lean_object* v___x_5293_ = _args[6];
lean_object* v___x_5294_ = _args[7];
lean_object* v___x_5295_ = _args[8];
lean_object* v_a_5296_ = _args[9];
lean_object* v___x_5297_ = _args[10];
lean_object* v___x_5298_ = _args[11];
lean_object* v___x_5299_ = _args[12];
lean_object* v_numParams_5300_ = _args[13];
lean_object* v_numFields_5301_ = _args[14];
lean_object* v___x_5302_ = _args[15];
lean_object* v_fields2_5303_ = _args[16];
lean_object* v_x_5304_ = _args[17];
lean_object* v___y_5305_ = _args[18];
lean_object* v___y_5306_ = _args[19];
lean_object* v___y_5307_ = _args[20];
lean_object* v___y_5308_ = _args[21];
lean_object* v___y_5309_ = _args[22];
_start:
{
uint8_t v_a_18343__boxed_5310_; uint8_t v___x_18344__boxed_5311_; lean_object* v_res_5312_; 
v_a_18343__boxed_5310_ = lean_unbox(v_a_5296_);
v___x_18344__boxed_5311_ = lean_unbox(v___x_5297_);
v_res_5312_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3(v_P_5287_, v_xs_5288_, v_fields1_5289_, v_head_5290_, v_tail_5291_, v_val_5292_, v___x_5293_, v___x_5294_, v___x_5295_, v_a_18343__boxed_5310_, v___x_18344__boxed_5311_, v___x_5298_, v___x_5299_, v_numParams_5300_, v_numFields_5301_, v___x_5302_, v_fields2_5303_, v_x_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_);
lean_dec(v___y_5308_);
lean_dec_ref(v___y_5307_);
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec_ref(v_x_5304_);
lean_dec_ref(v_fields1_5289_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4(lean_object* v_P_5313_, lean_object* v_xs_5314_, lean_object* v_head_5315_, lean_object* v_tail_5316_, lean_object* v_val_5317_, lean_object* v___x_5318_, lean_object* v___x_5319_, lean_object* v___x_5320_, uint8_t v_a_5321_, uint8_t v___x_5322_, lean_object* v___x_5323_, lean_object* v___x_5324_, lean_object* v_numParams_5325_, lean_object* v_numFields_5326_, lean_object* v___x_5327_, lean_object* v_t_5328_, lean_object* v___x_5329_, lean_object* v_fields1_5330_, lean_object* v_x_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___f_5339_; lean_object* v___x_5340_; 
v___x_5337_ = lean_box(v_a_5321_);
v___x_5338_ = lean_box(v___x_5322_);
v___f_5339_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__3___boxed), 23, 16);
lean_closure_set(v___f_5339_, 0, v_P_5313_);
lean_closure_set(v___f_5339_, 1, v_xs_5314_);
lean_closure_set(v___f_5339_, 2, v_fields1_5330_);
lean_closure_set(v___f_5339_, 3, v_head_5315_);
lean_closure_set(v___f_5339_, 4, v_tail_5316_);
lean_closure_set(v___f_5339_, 5, v_val_5317_);
lean_closure_set(v___f_5339_, 6, v___x_5318_);
lean_closure_set(v___f_5339_, 7, v___x_5319_);
lean_closure_set(v___f_5339_, 8, v___x_5320_);
lean_closure_set(v___f_5339_, 9, v___x_5337_);
lean_closure_set(v___f_5339_, 10, v___x_5338_);
lean_closure_set(v___f_5339_, 11, v___x_5323_);
lean_closure_set(v___f_5339_, 12, v___x_5324_);
lean_closure_set(v___f_5339_, 13, v_numParams_5325_);
lean_closure_set(v___f_5339_, 14, v_numFields_5326_);
lean_closure_set(v___f_5339_, 15, v___x_5327_);
v___x_5340_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5328_, v___x_5329_, v___f_5339_, v_a_5321_, v_a_5321_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_P_5341_ = _args[0];
lean_object* v_xs_5342_ = _args[1];
lean_object* v_head_5343_ = _args[2];
lean_object* v_tail_5344_ = _args[3];
lean_object* v_val_5345_ = _args[4];
lean_object* v___x_5346_ = _args[5];
lean_object* v___x_5347_ = _args[6];
lean_object* v___x_5348_ = _args[7];
lean_object* v_a_5349_ = _args[8];
lean_object* v___x_5350_ = _args[9];
lean_object* v___x_5351_ = _args[10];
lean_object* v___x_5352_ = _args[11];
lean_object* v_numParams_5353_ = _args[12];
lean_object* v_numFields_5354_ = _args[13];
lean_object* v___x_5355_ = _args[14];
lean_object* v_t_5356_ = _args[15];
lean_object* v___x_5357_ = _args[16];
lean_object* v_fields1_5358_ = _args[17];
lean_object* v_x_5359_ = _args[18];
lean_object* v___y_5360_ = _args[19];
lean_object* v___y_5361_ = _args[20];
lean_object* v___y_5362_ = _args[21];
lean_object* v___y_5363_ = _args[22];
lean_object* v___y_5364_ = _args[23];
_start:
{
uint8_t v_a_18426__boxed_5365_; uint8_t v___x_18427__boxed_5366_; lean_object* v_res_5367_; 
v_a_18426__boxed_5365_ = lean_unbox(v_a_5349_);
v___x_18427__boxed_5366_ = lean_unbox(v___x_5350_);
v_res_5367_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4(v_P_5341_, v_xs_5342_, v_head_5343_, v_tail_5344_, v_val_5345_, v___x_5346_, v___x_5347_, v___x_5348_, v_a_18426__boxed_5365_, v___x_18427__boxed_5366_, v___x_5351_, v___x_5352_, v_numParams_5353_, v_numFields_5354_, v___x_5355_, v_t_5356_, v___x_5357_, v_fields1_5358_, v_x_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
lean_dec(v___y_5361_);
lean_dec_ref(v___y_5360_);
lean_dec_ref(v_x_5359_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5(lean_object* v_numFields_5368_, lean_object* v_xs_5369_, lean_object* v_head_5370_, lean_object* v_tail_5371_, lean_object* v_val_5372_, lean_object* v___x_5373_, lean_object* v___x_5374_, lean_object* v___x_5375_, uint8_t v_a_5376_, uint8_t v___x_5377_, lean_object* v___x_5378_, lean_object* v___x_5379_, lean_object* v_numParams_5380_, lean_object* v___x_5381_, lean_object* v_t_5382_, lean_object* v_P_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___f_5392_; lean_object* v___x_5393_; 
lean_inc(v_numFields_5368_);
v___x_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5389_, 0, v_numFields_5368_);
v___x_5390_ = lean_box(v_a_5376_);
v___x_5391_ = lean_box(v___x_5377_);
lean_inc_ref(v___x_5389_);
lean_inc_ref(v_t_5382_);
v___f_5392_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__4___boxed), 24, 17);
lean_closure_set(v___f_5392_, 0, v_P_5383_);
lean_closure_set(v___f_5392_, 1, v_xs_5369_);
lean_closure_set(v___f_5392_, 2, v_head_5370_);
lean_closure_set(v___f_5392_, 3, v_tail_5371_);
lean_closure_set(v___f_5392_, 4, v_val_5372_);
lean_closure_set(v___f_5392_, 5, v___x_5373_);
lean_closure_set(v___f_5392_, 6, v___x_5374_);
lean_closure_set(v___f_5392_, 7, v___x_5375_);
lean_closure_set(v___f_5392_, 8, v___x_5390_);
lean_closure_set(v___f_5392_, 9, v___x_5391_);
lean_closure_set(v___f_5392_, 10, v___x_5378_);
lean_closure_set(v___f_5392_, 11, v___x_5379_);
lean_closure_set(v___f_5392_, 12, v_numParams_5380_);
lean_closure_set(v___f_5392_, 13, v_numFields_5368_);
lean_closure_set(v___f_5392_, 14, v___x_5381_);
lean_closure_set(v___f_5392_, 15, v_t_5382_);
lean_closure_set(v___f_5392_, 16, v___x_5389_);
v___x_5393_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_t_5382_, v___x_5389_, v___f_5392_, v_a_5376_, v_a_5376_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5___boxed(lean_object** _args){
lean_object* v_numFields_5394_ = _args[0];
lean_object* v_xs_5395_ = _args[1];
lean_object* v_head_5396_ = _args[2];
lean_object* v_tail_5397_ = _args[3];
lean_object* v_val_5398_ = _args[4];
lean_object* v___x_5399_ = _args[5];
lean_object* v___x_5400_ = _args[6];
lean_object* v___x_5401_ = _args[7];
lean_object* v_a_5402_ = _args[8];
lean_object* v___x_5403_ = _args[9];
lean_object* v___x_5404_ = _args[10];
lean_object* v___x_5405_ = _args[11];
lean_object* v_numParams_5406_ = _args[12];
lean_object* v___x_5407_ = _args[13];
lean_object* v_t_5408_ = _args[14];
lean_object* v_P_5409_ = _args[15];
lean_object* v___y_5410_ = _args[16];
lean_object* v___y_5411_ = _args[17];
lean_object* v___y_5412_ = _args[18];
lean_object* v___y_5413_ = _args[19];
lean_object* v___y_5414_ = _args[20];
_start:
{
uint8_t v_a_18488__boxed_5415_; uint8_t v___x_18489__boxed_5416_; lean_object* v_res_5417_; 
v_a_18488__boxed_5415_ = lean_unbox(v_a_5402_);
v___x_18489__boxed_5416_ = lean_unbox(v___x_5403_);
v_res_5417_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5(v_numFields_5394_, v_xs_5395_, v_head_5396_, v_tail_5397_, v_val_5398_, v___x_5399_, v___x_5400_, v___x_5401_, v_a_18488__boxed_5415_, v___x_18489__boxed_5416_, v___x_5404_, v___x_5405_, v_numParams_5406_, v___x_5407_, v_t_5408_, v_P_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_);
lean_dec(v___y_5413_);
lean_dec_ref(v___y_5412_);
lean_dec(v___y_5411_);
lean_dec_ref(v___y_5410_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6(lean_object* v_numFields_5418_, lean_object* v_head_5419_, lean_object* v_tail_5420_, lean_object* v_val_5421_, lean_object* v___x_5422_, lean_object* v___x_5423_, lean_object* v___x_5424_, uint8_t v_a_5425_, uint8_t v___x_5426_, lean_object* v___x_5427_, lean_object* v___x_5428_, lean_object* v_numParams_5429_, lean_object* v___x_5430_, lean_object* v_head_5431_, lean_object* v_xs_5432_, lean_object* v_t_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___f_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; 
v___x_5439_ = lean_box(v_a_5425_);
v___x_5440_ = lean_box(v___x_5426_);
v___f_5441_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__5___boxed), 21, 15);
lean_closure_set(v___f_5441_, 0, v_numFields_5418_);
lean_closure_set(v___f_5441_, 1, v_xs_5432_);
lean_closure_set(v___f_5441_, 2, v_head_5419_);
lean_closure_set(v___f_5441_, 3, v_tail_5420_);
lean_closure_set(v___f_5441_, 4, v_val_5421_);
lean_closure_set(v___f_5441_, 5, v___x_5422_);
lean_closure_set(v___f_5441_, 6, v___x_5423_);
lean_closure_set(v___f_5441_, 7, v___x_5424_);
lean_closure_set(v___f_5441_, 8, v___x_5439_);
lean_closure_set(v___f_5441_, 9, v___x_5440_);
lean_closure_set(v___f_5441_, 10, v___x_5427_);
lean_closure_set(v___f_5441_, 11, v___x_5428_);
lean_closure_set(v___f_5441_, 12, v_numParams_5429_);
lean_closure_set(v___f_5441_, 13, v___x_5430_);
lean_closure_set(v___f_5441_, 14, v_t_5433_);
v___x_5442_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_5443_ = l_Lean_Expr_sort___override(v_head_5431_);
v___x_5444_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5442_, v___x_5443_, v___f_5441_, v___y_5434_, v___y_5435_, v___y_5436_, v___y_5437_);
return v___x_5444_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_numFields_5445_ = _args[0];
lean_object* v_head_5446_ = _args[1];
lean_object* v_tail_5447_ = _args[2];
lean_object* v_val_5448_ = _args[3];
lean_object* v___x_5449_ = _args[4];
lean_object* v___x_5450_ = _args[5];
lean_object* v___x_5451_ = _args[6];
lean_object* v_a_5452_ = _args[7];
lean_object* v___x_5453_ = _args[8];
lean_object* v___x_5454_ = _args[9];
lean_object* v___x_5455_ = _args[10];
lean_object* v_numParams_5456_ = _args[11];
lean_object* v___x_5457_ = _args[12];
lean_object* v_head_5458_ = _args[13];
lean_object* v_xs_5459_ = _args[14];
lean_object* v_t_5460_ = _args[15];
lean_object* v___y_5461_ = _args[16];
lean_object* v___y_5462_ = _args[17];
lean_object* v___y_5463_ = _args[18];
lean_object* v___y_5464_ = _args[19];
lean_object* v___y_5465_ = _args[20];
_start:
{
uint8_t v_a_18549__boxed_5466_; uint8_t v___x_18550__boxed_5467_; lean_object* v_res_5468_; 
v_a_18549__boxed_5466_ = lean_unbox(v_a_5452_);
v___x_18550__boxed_5467_ = lean_unbox(v___x_5453_);
v_res_5468_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6(v_numFields_5445_, v_head_5446_, v_tail_5447_, v_val_5448_, v___x_5449_, v___x_5450_, v___x_5451_, v_a_18549__boxed_5466_, v___x_18550__boxed_5467_, v___x_5454_, v___x_5455_, v_numParams_5456_, v___x_5457_, v_head_5458_, v_xs_5459_, v_t_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
lean_dec(v___y_5464_);
lean_dec_ref(v___y_5463_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
return v_res_5468_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(lean_object* v_tail_5469_, lean_object* v_val_5470_, lean_object* v___x_5471_, lean_object* v___x_5472_, uint8_t v_a_5473_, lean_object* v___x_5474_, lean_object* v_head_5475_, lean_object* v_as_x27_5476_, lean_object* v_b_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
if (lean_obj_tag(v_as_x27_5476_) == 0)
{
lean_object* v___x_5483_; 
lean_dec(v_head_5475_);
lean_dec(v___x_5474_);
lean_dec(v___x_5472_);
lean_dec(v___x_5471_);
lean_dec_ref(v_val_5470_);
lean_dec(v_tail_5469_);
v___x_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5483_, 0, v_b_5477_);
return v___x_5483_;
}
else
{
lean_object* v_head_5484_; lean_object* v_tail_5485_; lean_object* v___x_5486_; 
v_head_5484_ = lean_ctor_get(v_as_x27_5476_, 0);
v_tail_5485_ = lean_ctor_get(v_as_x27_5476_, 1);
lean_inc(v_head_5484_);
v___x_5486_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0(v_head_5484_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; lean_object* v_toConstantVal_5488_; lean_object* v_numParams_5489_; lean_object* v_numFields_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; uint8_t v___x_5493_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_a_5487_);
lean_dec_ref_known(v___x_5486_, 1);
v_toConstantVal_5488_ = lean_ctor_get(v_a_5487_, 0);
lean_inc_ref(v_toConstantVal_5488_);
v_numParams_5489_ = lean_ctor_get(v_a_5487_, 3);
lean_inc(v_numParams_5489_);
v_numFields_5490_ = lean_ctor_get(v_a_5487_, 4);
lean_inc(v_numFields_5490_);
lean_dec(v_a_5487_);
v___x_5491_ = lean_box(0);
v___x_5492_ = lean_unsigned_to_nat(0u);
v___x_5493_ = lean_nat_dec_lt(v___x_5492_, v_numFields_5490_);
if (v___x_5493_ == 0)
{
lean_dec(v_numFields_5490_);
lean_dec(v_numParams_5489_);
lean_dec_ref(v_toConstantVal_5488_);
v_as_x27_5476_ = v_tail_5485_;
v_b_5477_ = v___x_5491_;
goto _start;
}
else
{
lean_object* v_type_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; lean_object* v___f_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_type_5495_ = lean_ctor_get(v_toConstantVal_5488_, 2);
lean_inc_ref(v_type_5495_);
lean_dec_ref(v_toConstantVal_5488_);
v___x_5496_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_5497_ = lean_box(v_a_5473_);
v___x_5498_ = lean_box(v___x_5493_);
lean_inc(v_head_5475_);
lean_inc(v_numParams_5489_);
lean_inc(v___x_5474_);
lean_inc(v___x_5472_);
lean_inc(v___x_5471_);
lean_inc_ref(v_val_5470_);
lean_inc(v_tail_5469_);
lean_inc(v_head_5484_);
v___f_5499_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___lam__6___boxed), 21, 14);
lean_closure_set(v___f_5499_, 0, v_numFields_5490_);
lean_closure_set(v___f_5499_, 1, v_head_5484_);
lean_closure_set(v___f_5499_, 2, v_tail_5469_);
lean_closure_set(v___f_5499_, 3, v_val_5470_);
lean_closure_set(v___f_5499_, 4, v___x_5471_);
lean_closure_set(v___f_5499_, 5, v___x_5472_);
lean_closure_set(v___f_5499_, 6, v___x_5492_);
lean_closure_set(v___f_5499_, 7, v___x_5497_);
lean_closure_set(v___f_5499_, 8, v___x_5498_);
lean_closure_set(v___f_5499_, 9, v___x_5496_);
lean_closure_set(v___f_5499_, 10, v___x_5474_);
lean_closure_set(v___f_5499_, 11, v_numParams_5489_);
lean_closure_set(v___f_5499_, 12, v___x_5491_);
lean_closure_set(v___f_5499_, 13, v_head_5475_);
v___x_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5500_, 0, v_numParams_5489_);
v___x_5501_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__4___redArg(v_type_5495_, v___x_5500_, v___f_5499_, v_a_5473_, v_a_5473_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_dec_ref_known(v___x_5501_, 1);
v_as_x27_5476_ = v_tail_5485_;
v_b_5477_ = v___x_5491_;
goto _start;
}
else
{
lean_dec(v_head_5475_);
lean_dec(v___x_5474_);
lean_dec(v___x_5472_);
lean_dec(v___x_5471_);
lean_dec_ref(v_val_5470_);
lean_dec(v_tail_5469_);
return v___x_5501_;
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
lean_dec(v_head_5475_);
lean_dec(v___x_5474_);
lean_dec(v___x_5472_);
lean_dec(v___x_5471_);
lean_dec_ref(v_val_5470_);
lean_dec(v_tail_5469_);
v_a_5503_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5486_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5486_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg___boxed(lean_object* v_tail_5511_, lean_object* v_val_5512_, lean_object* v___x_5513_, lean_object* v___x_5514_, lean_object* v_a_5515_, lean_object* v___x_5516_, lean_object* v_head_5517_, lean_object* v_as_x27_5518_, lean_object* v_b_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
uint8_t v_a_18612__boxed_5525_; lean_object* v_res_5526_; 
v_a_18612__boxed_5525_ = lean_unbox(v_a_5515_);
v_res_5526_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5511_, v_val_5512_, v___x_5513_, v___x_5514_, v_a_18612__boxed_5525_, v___x_5516_, v_head_5517_, v_as_x27_5518_, v_b_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
lean_dec(v_as_x27_5518_);
return v_res_5526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1(void){
_start:
{
lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5528_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__0));
v___x_5529_ = l_Lean_stringToMessageData(v___x_5528_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(lean_object* v_declName_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_){
_start:
{
lean_object* v___x_5536_; 
lean_inc(v_declName_5530_);
v___x_5536_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5614_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5614_ == 0)
{
v___x_5539_ = v___x_5536_;
v_isShared_5540_ = v_isSharedCheck_5614_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5614_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
if (lean_obj_tag(v_a_5537_) == 5)
{
lean_object* v_val_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
lean_del_object(v___x_5539_);
v_val_5541_ = lean_ctor_get(v_a_5537_, 0);
lean_inc_ref(v_val_5541_);
lean_dec_ref_known(v_a_5537_, 1);
lean_inc(v_declName_5530_);
v___x_5542_ = l_Lean_mkRecName(v_declName_5530_);
v___x_5543_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_5542_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
if (lean_obj_tag(v___x_5543_) == 0)
{
lean_object* v_toConstantVal_5544_; lean_object* v_a_5545_; lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5601_; 
v_toConstantVal_5544_ = lean_ctor_get(v_val_5541_, 0);
v_a_5545_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5601_ == 0)
{
v___x_5547_ = v___x_5543_;
v_isShared_5548_ = v_isSharedCheck_5601_;
goto v_resetjp_5546_;
}
else
{
lean_inc(v_a_5545_);
lean_dec(v___x_5543_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5601_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v_ctors_5549_; lean_object* v_levelParams_5550_; lean_object* v_type_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; uint8_t v___x_5555_; 
v_ctors_5549_ = lean_ctor_get(v_val_5541_, 4);
lean_inc(v_ctors_5549_);
v_levelParams_5550_ = lean_ctor_get(v_toConstantVal_5544_, 1);
v_type_5551_ = lean_ctor_get(v_toConstantVal_5544_, 2);
v___x_5552_ = l_List_lengthTR___redArg(v_levelParams_5550_);
v___x_5553_ = l_Lean_ConstantInfo_levelParams(v_a_5545_);
v___x_5554_ = l_List_lengthTR___redArg(v___x_5553_);
v___x_5555_ = lean_nat_dec_lt(v___x_5552_, v___x_5554_);
lean_dec(v___x_5554_);
lean_dec(v___x_5552_);
if (v___x_5555_ == 0)
{
lean_object* v___x_5556_; lean_object* v___x_5558_; 
lean_dec(v___x_5553_);
lean_dec(v_ctors_5549_);
lean_dec(v_a_5545_);
lean_dec_ref(v_val_5541_);
lean_dec(v_declName_5530_);
v___x_5556_ = lean_box(0);
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 0, v___x_5556_);
v___x_5558_ = v___x_5547_;
goto v_reusejp_5557_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v___x_5556_);
v___x_5558_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5557_;
}
v_reusejp_5557_:
{
return v___x_5558_;
}
}
else
{
lean_object* v___x_5560_; 
lean_del_object(v___x_5547_);
lean_inc_ref(v_type_5551_);
v___x_5560_ = l_Lean_Meta_isPropFormerType(v_type_5551_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
if (lean_obj_tag(v___x_5560_) == 0)
{
lean_object* v_a_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5592_; 
v_a_5561_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5563_ = v___x_5560_;
v_isShared_5564_ = v_isSharedCheck_5592_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_a_5561_);
lean_dec(v___x_5560_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5592_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
uint8_t v___x_5565_; 
v___x_5565_ = lean_unbox(v_a_5561_);
if (v___x_5565_ == 0)
{
lean_object* v___x_5566_; lean_object* v___x_5567_; 
lean_del_object(v___x_5563_);
v___x_5566_ = lean_box(0);
lean_inc(v___x_5553_);
v___x_5567_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v___x_5553_, v___x_5566_);
if (lean_obj_tag(v___x_5567_) == 1)
{
lean_object* v_head_5568_; lean_object* v_tail_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; uint8_t v___x_5573_; lean_object* v___x_5574_; 
lean_dec(v_a_5545_);
v_head_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_head_5568_);
v_tail_5569_ = lean_ctor_get(v___x_5567_, 1);
lean_inc(v_tail_5569_);
v___x_5570_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_5571_ = l_Lean_Name_str___override(v_declName_5530_, v___x_5570_);
v___x_5572_ = lean_box(0);
v___x_5573_ = lean_unbox(v_a_5561_);
lean_dec(v_a_5561_);
v___x_5574_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5569_, v_val_5541_, v___x_5571_, v___x_5567_, v___x_5573_, v___x_5553_, v_head_5568_, v_ctors_5549_, v___x_5572_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
lean_dec(v_ctors_5549_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v___x_5576_; uint8_t v_isShared_5577_; uint8_t v_isSharedCheck_5581_; 
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v___x_5574_, 0);
lean_dec(v_unused_5582_);
v___x_5576_ = v___x_5574_;
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
else
{
lean_dec(v___x_5574_);
v___x_5576_ = lean_box(0);
v_isShared_5577_ = v_isSharedCheck_5581_;
goto v_resetjp_5575_;
}
v_resetjp_5575_:
{
lean_object* v___x_5579_; 
if (v_isShared_5577_ == 0)
{
lean_ctor_set(v___x_5576_, 0, v___x_5572_);
v___x_5579_ = v___x_5576_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5572_);
v___x_5579_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
return v___x_5579_;
}
}
}
else
{
return v___x_5574_;
}
}
else
{
lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; lean_object* v___x_5587_; 
lean_dec(v___x_5567_);
lean_dec(v_a_5561_);
lean_dec(v___x_5553_);
lean_dec(v_ctors_5549_);
lean_dec_ref(v_val_5541_);
lean_dec(v_declName_5530_);
v___x_5583_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___closed__1);
v___x_5584_ = l_Lean_ConstantInfo_name(v_a_5545_);
lean_dec(v_a_5545_);
v___x_5585_ = l_Lean_MessageData_ofName(v___x_5584_);
v___x_5586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5583_);
lean_ctor_set(v___x_5586_, 1, v___x_5585_);
v___x_5587_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0___redArg(v___x_5586_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_);
return v___x_5587_;
}
}
else
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
lean_dec(v_a_5561_);
lean_dec(v___x_5553_);
lean_dec(v_ctors_5549_);
lean_dec(v_a_5545_);
lean_dec_ref(v_val_5541_);
lean_dec(v_declName_5530_);
v___x_5588_ = lean_box(0);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 0, v___x_5588_);
v___x_5590_ = v___x_5563_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5588_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec(v___x_5553_);
lean_dec(v_ctors_5549_);
lean_dec(v_a_5545_);
lean_dec_ref(v_val_5541_);
lean_dec(v_declName_5530_);
v_a_5593_ = lean_ctor_get(v___x_5560_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5560_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5560_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5560_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
}
}
}
else
{
lean_object* v_a_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5609_; 
lean_dec_ref(v_val_5541_);
lean_dec(v_declName_5530_);
v_a_5602_ = lean_ctor_get(v___x_5543_, 0);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5609_ == 0)
{
v___x_5604_ = v___x_5543_;
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_a_5602_);
lean_dec(v___x_5543_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5609_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v___x_5607_; 
if (v_isShared_5605_ == 0)
{
v___x_5607_ = v___x_5604_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5602_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
}
else
{
lean_object* v___x_5610_; lean_object* v___x_5612_; 
lean_dec(v_a_5537_);
lean_dec(v_declName_5530_);
v___x_5610_ = lean_box(0);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5610_);
v___x_5612_ = v___x_5539_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
v___x_5612_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
return v___x_5612_;
}
}
}
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec(v_declName_5530_);
v_a_5615_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5536_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5536_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors___boxed(lean_object* v_declName_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_){
_start:
{
lean_object* v_res_5629_; 
v_res_5629_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5623_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_);
lean_dec(v_a_5627_);
lean_dec_ref(v_a_5626_);
lean_dec(v_a_5625_);
lean_dec_ref(v_a_5624_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(lean_object* v_range_5630_, lean_object* v_b_5631_, lean_object* v_i_5632_, lean_object* v_hs_5633_, lean_object* v_hl_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_){
_start:
{
lean_object* v___x_5640_; 
v___x_5640_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___redArg(v_range_5630_, v_b_5631_, v_i_5632_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_);
return v___x_5640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0___boxed(lean_object* v_range_5641_, lean_object* v_b_5642_, lean_object* v_i_5643_, lean_object* v_hs_5644_, lean_object* v_hl_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
lean_object* v_res_5651_; 
v_res_5651_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__0(v_range_5641_, v_b_5642_, v_i_5643_, v_hs_5644_, v_hl_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
lean_dec(v___y_5649_);
lean_dec_ref(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec_ref(v_range_5641_);
return v_res_5651_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(lean_object* v_tail_5652_, lean_object* v_val_5653_, lean_object* v___x_5654_, lean_object* v___x_5655_, uint8_t v_a_5656_, lean_object* v___x_5657_, lean_object* v_head_5658_, lean_object* v_as_5659_, lean_object* v_as_x27_5660_, lean_object* v_b_5661_, lean_object* v_a_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_){
_start:
{
lean_object* v___x_5668_; 
v___x_5668_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___redArg(v_tail_5652_, v_val_5653_, v___x_5654_, v___x_5655_, v_a_5656_, v___x_5657_, v_head_5658_, v_as_x27_5660_, v_b_5661_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_);
return v___x_5668_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2___boxed(lean_object* v_tail_5669_, lean_object* v_val_5670_, lean_object* v___x_5671_, lean_object* v___x_5672_, lean_object* v_a_5673_, lean_object* v___x_5674_, lean_object* v_head_5675_, lean_object* v_as_5676_, lean_object* v_as_x27_5677_, lean_object* v_b_5678_, lean_object* v_a_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
uint8_t v_a_18896__boxed_5685_; lean_object* v_res_5686_; 
v_a_18896__boxed_5685_ = lean_unbox(v_a_5673_);
v_res_5686_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors_spec__2(v_tail_5669_, v_val_5670_, v___x_5671_, v___x_5672_, v_a_18896__boxed_5685_, v___x_5674_, v_head_5675_, v_as_5676_, v_as_x27_5677_, v_b_5678_, v_a_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_as_x27_5677_);
lean_dec(v_as_5676_);
return v_res_5686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(lean_object* v_declName_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_){
_start:
{
lean_object* v___x_5693_; 
lean_inc(v_declName_5687_);
v___x_5693_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
if (lean_obj_tag(v___x_5693_) == 0)
{
lean_object* v_a_5694_; lean_object* v___x_5696_; uint8_t v_isShared_5697_; uint8_t v_isSharedCheck_5751_; 
v_a_5694_ = lean_ctor_get(v___x_5693_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5693_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5696_ = v___x_5693_;
v_isShared_5697_ = v_isSharedCheck_5751_;
goto v_resetjp_5695_;
}
else
{
lean_inc(v_a_5694_);
lean_dec(v___x_5693_);
v___x_5696_ = lean_box(0);
v_isShared_5697_ = v_isSharedCheck_5751_;
goto v_resetjp_5695_;
}
v_resetjp_5695_:
{
if (lean_obj_tag(v_a_5694_) == 5)
{
lean_object* v_val_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
lean_del_object(v___x_5696_);
v_val_5698_ = lean_ctor_get(v_a_5694_, 0);
lean_inc_ref(v_val_5698_);
lean_dec_ref_known(v_a_5694_, 1);
lean_inc(v_declName_5687_);
v___x_5699_ = l_Lean_mkRecName(v_declName_5687_);
v___x_5700_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v___x_5699_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
if (lean_obj_tag(v___x_5700_) == 0)
{
lean_object* v_toConstantVal_5701_; lean_object* v_a_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5738_; 
v_toConstantVal_5701_ = lean_ctor_get(v_val_5698_, 0);
lean_inc_ref(v_toConstantVal_5701_);
lean_dec_ref(v_val_5698_);
v_a_5702_ = lean_ctor_get(v___x_5700_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5700_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5704_ = v___x_5700_;
v_isShared_5705_ = v_isSharedCheck_5738_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_a_5702_);
lean_dec(v___x_5700_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5738_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v_levelParams_5706_; lean_object* v_type_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; uint8_t v___x_5711_; 
v_levelParams_5706_ = lean_ctor_get(v_toConstantVal_5701_, 1);
lean_inc(v_levelParams_5706_);
v_type_5707_ = lean_ctor_get(v_toConstantVal_5701_, 2);
lean_inc_ref(v_type_5707_);
lean_dec_ref(v_toConstantVal_5701_);
v___x_5708_ = l_List_lengthTR___redArg(v_levelParams_5706_);
lean_dec(v_levelParams_5706_);
v___x_5709_ = l_Lean_ConstantInfo_levelParams(v_a_5702_);
lean_dec(v_a_5702_);
v___x_5710_ = l_List_lengthTR___redArg(v___x_5709_);
lean_dec(v___x_5709_);
v___x_5711_ = lean_nat_dec_lt(v___x_5708_, v___x_5710_);
lean_dec(v___x_5710_);
lean_dec(v___x_5708_);
if (v___x_5711_ == 0)
{
lean_object* v___x_5712_; lean_object* v___x_5714_; 
lean_dec_ref(v_type_5707_);
lean_dec(v_declName_5687_);
v___x_5712_ = lean_box(0);
if (v_isShared_5705_ == 0)
{
lean_ctor_set(v___x_5704_, 0, v___x_5712_);
v___x_5714_ = v___x_5704_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
else
{
lean_object* v___x_5716_; 
lean_del_object(v___x_5704_);
v___x_5716_ = l_Lean_Meta_isPropFormerType(v_type_5707_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
if (lean_obj_tag(v___x_5716_) == 0)
{
lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5729_; 
v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5729_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5729_ == 0)
{
v___x_5719_ = v___x_5716_;
v_isShared_5720_ = v_isSharedCheck_5729_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5716_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5729_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
uint8_t v___x_5721_; 
v___x_5721_ = lean_unbox(v_a_5717_);
lean_dec(v_a_5717_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5722_; 
lean_del_object(v___x_5719_);
lean_inc(v_declName_5687_);
v___x_5722_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType(v_declName_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_object* v___x_5723_; 
lean_dec_ref_known(v___x_5722_, 1);
lean_inc(v_declName_5687_);
v___x_5723_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp(v_declName_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v___x_5724_; 
lean_dec_ref_known(v___x_5723_, 1);
v___x_5724_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtors(v_declName_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
return v___x_5724_;
}
else
{
lean_dec(v_declName_5687_);
return v___x_5723_;
}
}
else
{
lean_dec(v_declName_5687_);
return v___x_5722_;
}
}
else
{
lean_object* v___x_5725_; lean_object* v___x_5727_; 
lean_dec(v_declName_5687_);
v___x_5725_ = lean_box(0);
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 0, v___x_5725_);
v___x_5727_ = v___x_5719_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v___x_5725_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
}
}
else
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec(v_declName_5687_);
v_a_5730_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5716_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5716_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
}
}
else
{
lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5746_; 
lean_dec_ref(v_val_5698_);
lean_dec(v_declName_5687_);
v_a_5739_ = lean_ctor_get(v___x_5700_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v___x_5700_);
if (v_isSharedCheck_5746_ == 0)
{
v___x_5741_ = v___x_5700_;
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5700_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5746_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5744_; 
if (v_isShared_5742_ == 0)
{
v___x_5744_ = v___x_5741_;
goto v_reusejp_5743_;
}
else
{
lean_object* v_reuseFailAlloc_5745_; 
v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
v___x_5744_ = v_reuseFailAlloc_5745_;
goto v_reusejp_5743_;
}
v_reusejp_5743_:
{
return v___x_5744_;
}
}
}
}
else
{
lean_object* v___x_5747_; lean_object* v___x_5749_; 
lean_dec(v_a_5694_);
lean_dec(v_declName_5687_);
v___x_5747_ = lean_box(0);
if (v_isShared_5697_ == 0)
{
lean_ctor_set(v___x_5696_, 0, v___x_5747_);
v___x_5749_ = v___x_5696_;
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
lean_dec(v_declName_5687_);
v_a_5752_ = lean_ctor_get(v___x_5693_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5693_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5754_ = v___x_5693_;
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5693_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore___boxed(lean_object* v_declName_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_, lean_object* v_a_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_);
lean_dec(v_a_5764_);
lean_dec_ref(v_a_5763_);
lean_dec(v_a_5762_);
lean_dec_ref(v_a_5761_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(lean_object* v_P_5770_, lean_object* v_x_5771_, lean_object* v___x_5772_, lean_object* v_enumName_5773_, lean_object* v_a_5774_, lean_object* v_levelParams_5775_, lean_object* v_val_5776_, lean_object* v___x_5777_, lean_object* v_y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; uint8_t v___x_5789_; uint8_t v___x_5790_; uint8_t v___x_5791_; lean_object* v___x_5792_; 
v___x_5784_ = lean_unsigned_to_nat(3u);
v___x_5785_ = lean_mk_empty_array_with_capacity(v___x_5784_);
lean_inc_ref(v_P_5770_);
v___x_5786_ = lean_array_push(v___x_5785_, v_P_5770_);
lean_inc_ref(v_x_5771_);
v___x_5787_ = lean_array_push(v___x_5786_, v_x_5771_);
lean_inc_ref(v_y_5778_);
v___x_5788_ = lean_array_push(v___x_5787_, v_y_5778_);
v___x_5789_ = 0;
v___x_5790_ = 1;
v___x_5791_ = 1;
v___x_5792_ = l_Lean_Meta_mkForallFVars(v___x_5788_, v___x_5772_, v___x_5789_, v___x_5790_, v___x_5790_, v___x_5791_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v_declValue_5795_; lean_object* v___y_5796_; lean_object* v___y_5797_; lean_object* v___y_5798_; lean_object* v___y_5799_; lean_object* v___x_5812_; lean_object* v___x_5813_; uint8_t v___x_5814_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref_known(v___x_5792_, 1);
v___x_5812_ = l_Lean_InductiveVal_numCtors(v_val_5776_);
v___x_5813_ = lean_unsigned_to_nat(1u);
v___x_5814_ = lean_nat_dec_eq(v___x_5812_, v___x_5813_);
lean_dec(v___x_5812_);
if (v___x_5814_ == 0)
{
lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
lean_inc(v_enumName_5773_);
v___x_5815_ = l_mkCtorIdxName(v_enumName_5773_);
v___x_5816_ = l_Lean_mkConst(v___x_5815_, v___x_5777_);
v___x_5817_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___closed__1));
v___x_5818_ = lean_unsigned_to_nat(4u);
v___x_5819_ = lean_mk_empty_array_with_capacity(v___x_5818_);
v___x_5820_ = lean_array_push(v___x_5819_, v___x_5816_);
v___x_5821_ = lean_array_push(v___x_5820_, v_P_5770_);
v___x_5822_ = lean_array_push(v___x_5821_, v_x_5771_);
v___x_5823_ = lean_array_push(v___x_5822_, v_y_5778_);
v___x_5824_ = l_Lean_Meta_mkAppM(v___x_5817_, v___x_5823_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5824_) == 0)
{
lean_object* v_a_5825_; lean_object* v___x_5826_; 
v_a_5825_ = lean_ctor_get(v___x_5824_, 0);
lean_inc(v_a_5825_);
lean_dec_ref_known(v___x_5824_, 1);
v___x_5826_ = l_Lean_Meta_mkLambdaFVars(v___x_5788_, v_a_5825_, v___x_5789_, v___x_5790_, v___x_5789_, v___x_5790_, v___x_5791_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec_ref(v___x_5788_);
if (lean_obj_tag(v___x_5826_) == 0)
{
lean_object* v_a_5827_; 
v_a_5827_ = lean_ctor_get(v___x_5826_, 0);
lean_inc(v_a_5827_);
lean_dec_ref_known(v___x_5826_, 1);
v_declValue_5795_ = v_a_5827_;
v___y_5796_ = v___y_5779_;
v___y_5797_ = v___y_5780_;
v___y_5798_ = v___y_5781_;
v___y_5799_ = v___y_5782_;
goto v___jp_5794_;
}
else
{
lean_object* v_a_5828_; lean_object* v___x_5830_; uint8_t v_isShared_5831_; uint8_t v_isSharedCheck_5835_; 
lean_dec(v_a_5793_);
lean_dec(v_levelParams_5775_);
lean_dec(v_a_5774_);
lean_dec(v_enumName_5773_);
v_a_5828_ = lean_ctor_get(v___x_5826_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5826_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5830_ = v___x_5826_;
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
else
{
lean_inc(v_a_5828_);
lean_dec(v___x_5826_);
v___x_5830_ = lean_box(0);
v_isShared_5831_ = v_isSharedCheck_5835_;
goto v_resetjp_5829_;
}
v_resetjp_5829_:
{
lean_object* v___x_5833_; 
if (v_isShared_5831_ == 0)
{
v___x_5833_ = v___x_5830_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5828_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec(v_a_5793_);
lean_dec_ref(v___x_5788_);
lean_dec(v_levelParams_5775_);
lean_dec(v_a_5774_);
lean_dec(v_enumName_5773_);
v_a_5836_ = lean_ctor_get(v___x_5824_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5824_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5824_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5824_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
else
{
lean_object* v___x_5844_; 
lean_dec_ref(v_y_5778_);
lean_dec(v___x_5777_);
lean_dec_ref(v_x_5771_);
lean_inc_ref(v_P_5770_);
v___x_5844_ = l_Lean_mkArrow(v_P_5770_, v_P_5770_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5844_) == 0)
{
lean_object* v_a_5845_; lean_object* v___x_5846_; 
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
lean_inc(v_a_5845_);
lean_dec_ref_known(v___x_5844_, 1);
v___x_5846_ = l_Lean_Meta_mkLambdaFVars(v___x_5788_, v_a_5845_, v___x_5789_, v___x_5790_, v___x_5789_, v___x_5790_, v___x_5791_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec_ref(v___x_5788_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
lean_inc(v_a_5847_);
lean_dec_ref_known(v___x_5846_, 1);
v_declValue_5795_ = v_a_5847_;
v___y_5796_ = v___y_5779_;
v___y_5797_ = v___y_5780_;
v___y_5798_ = v___y_5781_;
v___y_5799_ = v___y_5782_;
goto v___jp_5794_;
}
else
{
lean_object* v_a_5848_; lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5855_; 
lean_dec(v_a_5793_);
lean_dec(v_levelParams_5775_);
lean_dec(v_a_5774_);
lean_dec(v_enumName_5773_);
v_a_5848_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5855_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5855_ == 0)
{
v___x_5850_ = v___x_5846_;
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
else
{
lean_inc(v_a_5848_);
lean_dec(v___x_5846_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v___x_5853_; 
if (v_isShared_5851_ == 0)
{
v___x_5853_ = v___x_5850_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
v___x_5853_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
return v___x_5853_;
}
}
}
}
else
{
lean_object* v_a_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5863_; 
lean_dec(v_a_5793_);
lean_dec_ref(v___x_5788_);
lean_dec(v_levelParams_5775_);
lean_dec(v_a_5774_);
lean_dec(v_enumName_5773_);
v_a_5856_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5858_ = v___x_5844_;
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_a_5856_);
lean_dec(v___x_5844_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5863_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
lean_object* v___x_5861_; 
if (v_isShared_5859_ == 0)
{
v___x_5861_ = v___x_5858_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_a_5856_);
v___x_5861_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
return v___x_5861_;
}
}
}
}
v___jp_5794_:
{
lean_object* v___x_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; uint8_t v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5800_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_5801_ = l_Lean_Name_str___override(v_enumName_5773_, v___x_5800_);
v___x_5802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5802_, 0, v_a_5774_);
lean_ctor_set(v___x_5802_, 1, v_levelParams_5775_);
lean_inc_n(v___x_5801_, 2);
v___x_5803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5803_, 0, v___x_5801_);
lean_ctor_set(v___x_5803_, 1, v___x_5802_);
lean_ctor_set(v___x_5803_, 2, v_a_5793_);
v___x_5804_ = lean_box(1);
v___x_5805_ = 1;
v___x_5806_ = lean_box(0);
v___x_5807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5807_, 0, v___x_5801_);
lean_ctor_set(v___x_5807_, 1, v___x_5806_);
v___x_5808_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5808_, 0, v___x_5803_);
lean_ctor_set(v___x_5808_, 1, v_declValue_5795_);
lean_ctor_set(v___x_5808_, 2, v___x_5804_);
lean_ctor_set(v___x_5808_, 3, v___x_5807_);
lean_ctor_set_uint8(v___x_5808_, sizeof(void*)*4, v___x_5805_);
v___x_5809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5809_, 0, v___x_5808_);
v___x_5810_ = l_Lean_addDecl(v___x_5809_, v___x_5789_, v___y_5798_, v___y_5799_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v___x_5811_; 
lean_dec_ref_known(v___x_5810_, 1);
v___x_5811_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_5801_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_);
return v___x_5811_;
}
else
{
lean_dec(v___x_5801_);
return v___x_5810_;
}
}
}
else
{
lean_object* v_a_5864_; lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5871_; 
lean_dec_ref(v___x_5788_);
lean_dec_ref(v_y_5778_);
lean_dec(v___x_5777_);
lean_dec(v_levelParams_5775_);
lean_dec(v_a_5774_);
lean_dec(v_enumName_5773_);
lean_dec_ref(v_x_5771_);
lean_dec_ref(v_P_5770_);
v_a_5864_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5866_ = v___x_5792_;
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
else
{
lean_inc(v_a_5864_);
lean_dec(v___x_5792_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v___x_5869_; 
if (v_isShared_5867_ == 0)
{
v___x_5869_ = v___x_5866_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed(lean_object* v_P_5872_, lean_object* v_x_5873_, lean_object* v___x_5874_, lean_object* v_enumName_5875_, lean_object* v_a_5876_, lean_object* v_levelParams_5877_, lean_object* v_val_5878_, lean_object* v___x_5879_, lean_object* v_y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_){
_start:
{
lean_object* v_res_5886_; 
v_res_5886_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0(v_P_5872_, v_x_5873_, v___x_5874_, v_enumName_5875_, v_a_5876_, v_levelParams_5877_, v_val_5878_, v___x_5879_, v_y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
lean_dec(v___y_5884_);
lean_dec_ref(v___y_5883_);
lean_dec(v___y_5882_);
lean_dec_ref(v___y_5881_);
lean_dec_ref(v_val_5878_);
return v_res_5886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(lean_object* v_P_5890_, lean_object* v___x_5891_, lean_object* v_enumName_5892_, lean_object* v_a_5893_, lean_object* v_levelParams_5894_, lean_object* v_val_5895_, lean_object* v___x_5896_, lean_object* v___x_5897_, lean_object* v_x_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_){
_start:
{
lean_object* v___f_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___f_5904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__0___boxed), 14, 8);
lean_closure_set(v___f_5904_, 0, v_P_5890_);
lean_closure_set(v___f_5904_, 1, v_x_5898_);
lean_closure_set(v___f_5904_, 2, v___x_5891_);
lean_closure_set(v___f_5904_, 3, v_enumName_5892_);
lean_closure_set(v___f_5904_, 4, v_a_5893_);
lean_closure_set(v___f_5904_, 5, v_levelParams_5894_);
lean_closure_set(v___f_5904_, 6, v_val_5895_);
lean_closure_set(v___f_5904_, 7, v___x_5896_);
v___x_5905_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_5906_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5905_, v___x_5897_, v___f_5904_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed(lean_object* v_P_5907_, lean_object* v___x_5908_, lean_object* v_enumName_5909_, lean_object* v_a_5910_, lean_object* v_levelParams_5911_, lean_object* v_val_5912_, lean_object* v___x_5913_, lean_object* v___x_5914_, lean_object* v_x_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1(v_P_5907_, v___x_5908_, v_enumName_5909_, v_a_5910_, v_levelParams_5911_, v_val_5912_, v___x_5913_, v___x_5914_, v_x_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(lean_object* v___x_5925_, lean_object* v_enumName_5926_, lean_object* v_a_5927_, lean_object* v_levelParams_5928_, lean_object* v_val_5929_, lean_object* v___x_5930_, lean_object* v___x_5931_, lean_object* v_P_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_){
_start:
{
lean_object* v___f_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
lean_inc_ref(v___x_5931_);
v___f_5938_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___boxed), 14, 8);
lean_closure_set(v___f_5938_, 0, v_P_5932_);
lean_closure_set(v___f_5938_, 1, v___x_5925_);
lean_closure_set(v___f_5938_, 2, v_enumName_5926_);
lean_closure_set(v___f_5938_, 3, v_a_5927_);
lean_closure_set(v___f_5938_, 4, v_levelParams_5928_);
lean_closure_set(v___f_5938_, 5, v_val_5929_);
lean_closure_set(v___f_5938_, 6, v___x_5930_);
lean_closure_set(v___f_5938_, 7, v___x_5931_);
v___x_5939_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_5940_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5939_, v___x_5931_, v___f_5938_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_);
return v___x_5940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed(lean_object* v___x_5941_, lean_object* v_enumName_5942_, lean_object* v_a_5943_, lean_object* v_levelParams_5944_, lean_object* v_val_5945_, lean_object* v___x_5946_, lean_object* v___x_5947_, lean_object* v_P_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2(v___x_5941_, v_enumName_5942_, v_a_5943_, v_levelParams_5944_, v_val_5945_, v___x_5946_, v___x_5947_, v_P_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
return v_res_5954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v___x_5959_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_5960_ = lean_unsigned_to_nat(63u);
v___x_5961_ = lean_unsigned_to_nat(376u);
v___x_5962_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__2));
v___x_5963_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_5964_ = l_mkPanicMessageWithDecl(v___x_5963_, v___x_5962_, v___x_5961_, v___x_5960_, v___x_5959_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(lean_object* v_enumName_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_){
_start:
{
lean_object* v___x_5971_; 
lean_inc(v_enumName_5965_);
v___x_5971_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
if (lean_obj_tag(v_a_5972_) == 5)
{
lean_object* v_val_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; 
v_val_5973_ = lean_ctor_get(v_a_5972_, 0);
lean_inc_ref(v_val_5973_);
lean_dec_ref_known(v_a_5972_, 1);
v___x_5974_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_5975_ = l_Lean_Core_mkFreshUserName(v___x_5974_, v_a_5968_, v_a_5969_);
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v_toConstantVal_5976_; lean_object* v_a_5977_; lean_object* v_levelParams_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___f_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; 
v_toConstantVal_5976_ = lean_ctor_get(v_val_5973_, 0);
v_a_5977_ = lean_ctor_get(v___x_5975_, 0);
lean_inc_n(v_a_5977_, 2);
lean_dec_ref_known(v___x_5975_, 1);
v_levelParams_5978_ = lean_ctor_get(v_toConstantVal_5976_, 1);
lean_inc_n(v_levelParams_5978_, 2);
v___x_5979_ = lean_box(0);
v___x_5980_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_5978_, v___x_5979_);
lean_inc(v___x_5980_);
lean_inc(v_enumName_5965_);
v___x_5981_ = l_Lean_mkConst(v_enumName_5965_, v___x_5980_);
v___x_5982_ = l_Lean_mkLevelParam(v_a_5977_);
v___x_5983_ = l_Lean_mkSort(v___x_5982_);
lean_inc_ref(v___x_5983_);
v___f_5984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___boxed), 13, 7);
lean_closure_set(v___f_5984_, 0, v___x_5983_);
lean_closure_set(v___f_5984_, 1, v_enumName_5965_);
lean_closure_set(v___f_5984_, 2, v_a_5977_);
lean_closure_set(v___f_5984_, 3, v_levelParams_5978_);
lean_closure_set(v___f_5984_, 4, v_val_5973_);
lean_closure_set(v___f_5984_, 5, v___x_5980_);
lean_closure_set(v___f_5984_, 6, v___x_5981_);
v___x_5985_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_5986_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_5985_, v___x_5983_, v___f_5984_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5986_;
}
else
{
lean_object* v_a_5987_; lean_object* v___x_5989_; uint8_t v_isShared_5990_; uint8_t v_isSharedCheck_5994_; 
lean_dec_ref(v_val_5973_);
lean_dec(v_enumName_5965_);
v_a_5987_ = lean_ctor_get(v___x_5975_, 0);
v_isSharedCheck_5994_ = !lean_is_exclusive(v___x_5975_);
if (v_isSharedCheck_5994_ == 0)
{
v___x_5989_ = v___x_5975_;
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
else
{
lean_inc(v_a_5987_);
lean_dec(v___x_5975_);
v___x_5989_ = lean_box(0);
v_isShared_5990_ = v_isSharedCheck_5994_;
goto v_resetjp_5988_;
}
v_resetjp_5988_:
{
lean_object* v___x_5992_; 
if (v_isShared_5990_ == 0)
{
v___x_5992_ = v___x_5989_;
goto v_reusejp_5991_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_a_5987_);
v___x_5992_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5991_;
}
v_reusejp_5991_:
{
return v___x_5992_;
}
}
}
}
else
{
lean_object* v___x_5995_; lean_object* v___x_5996_; 
lean_dec(v_a_5972_);
lean_dec(v_enumName_5965_);
v___x_5995_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__3);
v___x_5996_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_5995_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5996_;
}
}
else
{
lean_object* v_a_5997_; lean_object* v___x_5999_; uint8_t v_isShared_6000_; uint8_t v_isSharedCheck_6004_; 
lean_dec(v_enumName_5965_);
v_a_5997_ = lean_ctor_get(v___x_5971_, 0);
v_isSharedCheck_6004_ = !lean_is_exclusive(v___x_5971_);
if (v_isSharedCheck_6004_ == 0)
{
v___x_5999_ = v___x_5971_;
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
else
{
lean_inc(v_a_5997_);
lean_dec(v___x_5971_);
v___x_5999_ = lean_box(0);
v_isShared_6000_ = v_isSharedCheck_6004_;
goto v_resetjp_5998_;
}
v_resetjp_5998_:
{
lean_object* v___x_6002_; 
if (v_isShared_6000_ == 0)
{
v___x_6002_ = v___x_5999_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v_a_5997_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
return v___x_6002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___boxed(lean_object* v_enumName_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
lean_dec(v_a_6007_);
lean_dec_ref(v_a_6006_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(uint8_t v___x_6012_, uint8_t v___x_6013_, uint8_t v___x_6014_, lean_object* v_p_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_){
_start:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6021_ = lean_unsigned_to_nat(1u);
v___x_6022_ = lean_mk_empty_array_with_capacity(v___x_6021_);
lean_inc_ref(v_p_6015_);
v___x_6023_ = lean_array_push(v___x_6022_, v_p_6015_);
v___x_6024_ = l_Lean_Meta_mkLambdaFVars(v___x_6023_, v_p_6015_, v___x_6012_, v___x_6013_, v___x_6012_, v___x_6013_, v___x_6014_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
lean_dec_ref(v___x_6023_);
return v___x_6024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed(lean_object* v___x_6025_, lean_object* v___x_6026_, lean_object* v___x_6027_, lean_object* v_p_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
uint8_t v___x_4259__boxed_6034_; uint8_t v___x_4260__boxed_6035_; uint8_t v___x_4261__boxed_6036_; lean_object* v_res_6037_; 
v___x_4259__boxed_6034_ = lean_unbox(v___x_6025_);
v___x_4260__boxed_6035_ = lean_unbox(v___x_6026_);
v___x_4261__boxed_6036_ = lean_unbox(v___x_6027_);
v_res_6037_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0(v___x_4259__boxed_6034_, v___x_4260__boxed_6035_, v___x_4261__boxed_6036_, v_p_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_);
lean_dec(v___y_6032_);
lean_dec_ref(v___y_6031_);
lean_dec(v___y_6030_);
lean_dec_ref(v___y_6029_);
return v_res_6037_;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3(void){
_start:
{
lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
v___x_6045_ = lean_box(0);
v___x_6046_ = lean_unsigned_to_nat(8u);
v___x_6047_ = lean_mk_empty_array_with_capacity(v___x_6046_);
v___x_6048_ = lean_array_push(v___x_6047_, v___x_6045_);
return v___x_6048_;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4(void){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
v___x_6049_ = lean_box(0);
v___x_6050_ = lean_obj_once(&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3, &l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3_once, _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__3);
v___x_6051_ = lean_array_push(v___x_6050_, v___x_6049_);
return v___x_6051_;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5(void){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; 
v___x_6052_ = lean_box(0);
v___x_6053_ = lean_obj_once(&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4, &l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4_once, _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__4);
v___x_6054_ = lean_array_push(v___x_6053_, v___x_6052_);
return v___x_6054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(lean_object* v_P_6058_, lean_object* v_x_6059_, lean_object* v_b_6060_, lean_object* v___x_6061_, uint8_t v___x_6062_, lean_object* v_enumName_6063_, lean_object* v_a_6064_, lean_object* v___x_6065_, lean_object* v_val_6066_, lean_object* v___x_6067_, lean_object* v_h_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_){
_start:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; uint8_t v___x_6081_; uint8_t v___x_6082_; lean_object* v___x_6083_; 
v___x_6074_ = lean_unsigned_to_nat(4u);
v___x_6075_ = lean_mk_empty_array_with_capacity(v___x_6074_);
lean_inc_ref_n(v_P_6058_, 2);
v___x_6076_ = lean_array_push(v___x_6075_, v_P_6058_);
lean_inc_ref_n(v_x_6059_, 2);
v___x_6077_ = lean_array_push(v___x_6076_, v_x_6059_);
lean_inc_ref_n(v_b_6060_, 2);
v___x_6078_ = lean_array_push(v___x_6077_, v_b_6060_);
lean_inc_ref(v_h_6068_);
v___x_6079_ = lean_array_push(v___x_6078_, v_h_6068_);
v___x_6080_ = l_Lean_mkApp3(v___x_6061_, v_P_6058_, v_x_6059_, v_b_6060_);
v___x_6081_ = 0;
v___x_6082_ = 1;
v___x_6083_ = l_Lean_Meta_mkForallFVars(v___x_6079_, v___x_6080_, v___x_6081_, v___x_6082_, v___x_6082_, v___x_6062_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
if (lean_obj_tag(v___x_6083_) == 0)
{
lean_object* v_a_6084_; lean_object* v_____do__lift_6086_; lean_object* v___y_6087_; lean_object* v___y_6088_; lean_object* v___y_6089_; lean_object* v___y_6090_; lean_object* v___x_6158_; lean_object* v___x_6159_; uint8_t v___x_6160_; 
v_a_6084_ = lean_ctor_get(v___x_6083_, 0);
lean_inc(v_a_6084_);
lean_dec_ref_known(v___x_6083_, 1);
v___x_6158_ = l_Lean_InductiveVal_numCtors(v_val_6066_);
v___x_6159_ = lean_unsigned_to_nat(1u);
v___x_6160_ = lean_nat_dec_eq(v___x_6158_, v___x_6159_);
lean_dec(v___x_6158_);
if (v___x_6160_ == 0)
{
lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v___x_6161_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6067_);
v___x_6163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6163_, 0, v_P_6058_);
v___x_6164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6164_, 0, v_x_6059_);
v___x_6165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6165_, 0, v_b_6060_);
v___x_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6166_, 0, v_h_6068_);
v___x_6167_ = lean_obj_once(&l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5, &l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5_once, _init_l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__5);
v___x_6168_ = lean_array_push(v___x_6167_, v___x_6162_);
v___x_6169_ = lean_array_push(v___x_6168_, v___x_6163_);
v___x_6170_ = lean_array_push(v___x_6169_, v___x_6164_);
v___x_6171_ = lean_array_push(v___x_6170_, v___x_6165_);
v___x_6172_ = lean_array_push(v___x_6171_, v___x_6166_);
v___x_6173_ = l_Lean_Meta_mkAppOptM(v___x_6161_, v___x_6172_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_object* v_a_6174_; 
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_a_6174_);
lean_dec_ref_known(v___x_6173_, 1);
v_____do__lift_6086_ = v_a_6174_;
v___y_6087_ = v___y_6069_;
v___y_6088_ = v___y_6070_;
v___y_6089_ = v___y_6071_;
v___y_6090_ = v___y_6072_;
goto v___jp_6085_;
}
else
{
lean_object* v_a_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6182_; 
lean_dec(v_a_6084_);
lean_dec_ref(v___x_6079_);
lean_dec(v___x_6065_);
lean_dec(v_a_6064_);
lean_dec(v_enumName_6063_);
v_a_6175_ = lean_ctor_get(v___x_6173_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6173_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6177_ = v___x_6173_;
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_a_6175_);
lean_dec(v___x_6173_);
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
else
{
lean_object* v___x_6183_; lean_object* v___x_6184_; lean_object* v___x_6185_; lean_object* v___f_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; 
lean_dec_ref(v_h_6068_);
lean_dec_ref(v___x_6067_);
lean_dec_ref(v_b_6060_);
lean_dec_ref(v_x_6059_);
v___x_6183_ = lean_box(v___x_6081_);
v___x_6184_ = lean_box(v___x_6082_);
v___x_6185_ = lean_box(v___x_6062_);
v___f_6186_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__0___boxed), 9, 3);
lean_closure_set(v___f_6186_, 0, v___x_6183_);
lean_closure_set(v___f_6186_, 1, v___x_6184_);
lean_closure_set(v___f_6186_, 2, v___x_6185_);
v___x_6187_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__7));
v___x_6188_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6187_, v_P_6058_, v___f_6186_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
if (lean_obj_tag(v___x_6188_) == 0)
{
lean_object* v_a_6189_; 
v_a_6189_ = lean_ctor_get(v___x_6188_, 0);
lean_inc(v_a_6189_);
lean_dec_ref_known(v___x_6188_, 1);
v_____do__lift_6086_ = v_a_6189_;
v___y_6087_ = v___y_6069_;
v___y_6088_ = v___y_6070_;
v___y_6089_ = v___y_6071_;
v___y_6090_ = v___y_6072_;
goto v___jp_6085_;
}
else
{
lean_object* v_a_6190_; lean_object* v___x_6192_; uint8_t v_isShared_6193_; uint8_t v_isSharedCheck_6197_; 
lean_dec(v_a_6084_);
lean_dec_ref(v___x_6079_);
lean_dec(v___x_6065_);
lean_dec(v_a_6064_);
lean_dec(v_enumName_6063_);
v_a_6190_ = lean_ctor_get(v___x_6188_, 0);
v_isSharedCheck_6197_ = !lean_is_exclusive(v___x_6188_);
if (v_isSharedCheck_6197_ == 0)
{
v___x_6192_ = v___x_6188_;
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
else
{
lean_inc(v_a_6190_);
lean_dec(v___x_6188_);
v___x_6192_ = lean_box(0);
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
v_resetjp_6191_:
{
lean_object* v___x_6195_; 
if (v_isShared_6193_ == 0)
{
v___x_6195_ = v___x_6192_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6196_; 
v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
v___x_6195_ = v_reuseFailAlloc_6196_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
return v___x_6195_;
}
}
}
}
v___jp_6085_:
{
lean_object* v___x_6091_; 
v___x_6091_ = l_Lean_Meta_mkLambdaFVars(v___x_6079_, v_____do__lift_6086_, v___x_6081_, v___x_6082_, v___x_6081_, v___x_6082_, v___x_6062_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
lean_dec_ref(v___x_6079_);
if (lean_obj_tag(v___x_6091_) == 0)
{
lean_object* v_a_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; uint8_t v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v_a_6092_ = lean_ctor_get(v___x_6091_, 0);
lean_inc(v_a_6092_);
lean_dec_ref_known(v___x_6091_, 1);
v___x_6093_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__0));
v___x_6094_ = l_Lean_Name_str___override(v_enumName_6063_, v___x_6093_);
v___x_6095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6095_, 0, v_a_6064_);
lean_ctor_set(v___x_6095_, 1, v___x_6065_);
lean_inc_n(v___x_6094_, 2);
v___x_6096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6096_, 0, v___x_6094_);
lean_ctor_set(v___x_6096_, 1, v___x_6095_);
lean_ctor_set(v___x_6096_, 2, v_a_6084_);
v___x_6097_ = lean_box(1);
v___x_6098_ = 1;
v___x_6099_ = lean_box(0);
v___x_6100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6100_, 0, v___x_6094_);
lean_ctor_set(v___x_6100_, 1, v___x_6099_);
v___x_6101_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_6101_, 0, v___x_6096_);
lean_ctor_set(v___x_6101_, 1, v_a_6092_);
lean_ctor_set(v___x_6101_, 2, v___x_6097_);
lean_ctor_set(v___x_6101_, 3, v___x_6100_);
lean_ctor_set_uint8(v___x_6101_, sizeof(void*)*4, v___x_6098_);
v___x_6102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6101_);
v___x_6103_ = l_Lean_addDecl(v___x_6102_, v___x_6081_, v___y_6089_, v___y_6090_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v___x_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6148_; 
lean_dec_ref_known(v___x_6103_, 1);
lean_inc(v___x_6094_);
v___x_6104_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7(v___x_6094_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_);
v_isSharedCheck_6148_ = !lean_is_exclusive(v___x_6104_);
if (v_isSharedCheck_6148_ == 0)
{
lean_object* v_unused_6149_; 
v_unused_6149_ = lean_ctor_get(v___x_6104_, 0);
lean_dec(v_unused_6149_);
v___x_6106_ = v___x_6104_;
v_isShared_6107_ = v_isSharedCheck_6148_;
goto v_resetjp_6105_;
}
else
{
lean_dec(v___x_6104_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6148_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6108_; lean_object* v_env_6109_; lean_object* v_nextMacroScope_6110_; lean_object* v_ngen_6111_; lean_object* v_auxDeclNGen_6112_; lean_object* v_traceState_6113_; lean_object* v_messages_6114_; lean_object* v_infoState_6115_; lean_object* v_snapshotTasks_6116_; lean_object* v___x_6118_; uint8_t v_isShared_6119_; uint8_t v_isSharedCheck_6146_; 
v___x_6108_ = lean_st_ref_take(v___y_6090_);
v_env_6109_ = lean_ctor_get(v___x_6108_, 0);
v_nextMacroScope_6110_ = lean_ctor_get(v___x_6108_, 1);
v_ngen_6111_ = lean_ctor_get(v___x_6108_, 2);
v_auxDeclNGen_6112_ = lean_ctor_get(v___x_6108_, 3);
v_traceState_6113_ = lean_ctor_get(v___x_6108_, 4);
v_messages_6114_ = lean_ctor_get(v___x_6108_, 6);
v_infoState_6115_ = lean_ctor_get(v___x_6108_, 7);
v_snapshotTasks_6116_ = lean_ctor_get(v___x_6108_, 8);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6108_);
if (v_isSharedCheck_6146_ == 0)
{
lean_object* v_unused_6147_; 
v_unused_6147_ = lean_ctor_get(v___x_6108_, 5);
lean_dec(v_unused_6147_);
v___x_6118_ = v___x_6108_;
v_isShared_6119_ = v_isSharedCheck_6146_;
goto v_resetjp_6117_;
}
else
{
lean_inc(v_snapshotTasks_6116_);
lean_inc(v_infoState_6115_);
lean_inc(v_messages_6114_);
lean_inc(v_traceState_6113_);
lean_inc(v_auxDeclNGen_6112_);
lean_inc(v_ngen_6111_);
lean_inc(v_nextMacroScope_6110_);
lean_inc(v_env_6109_);
lean_dec(v___x_6108_);
v___x_6118_ = lean_box(0);
v_isShared_6119_ = v_isSharedCheck_6146_;
goto v_resetjp_6117_;
}
v_resetjp_6117_:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6124_; 
v___x_6120_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__0));
v___x_6121_ = l_Lean_markNoConfusion(v_env_6109_, v___x_6094_, v___x_6120_);
v___x_6122_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__2);
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 5, v___x_6122_);
lean_ctor_set(v___x_6118_, 0, v___x_6121_);
v___x_6124_ = v___x_6118_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v___x_6121_);
lean_ctor_set(v_reuseFailAlloc_6145_, 1, v_nextMacroScope_6110_);
lean_ctor_set(v_reuseFailAlloc_6145_, 2, v_ngen_6111_);
lean_ctor_set(v_reuseFailAlloc_6145_, 3, v_auxDeclNGen_6112_);
lean_ctor_set(v_reuseFailAlloc_6145_, 4, v_traceState_6113_);
lean_ctor_set(v_reuseFailAlloc_6145_, 5, v___x_6122_);
lean_ctor_set(v_reuseFailAlloc_6145_, 6, v_messages_6114_);
lean_ctor_set(v_reuseFailAlloc_6145_, 7, v_infoState_6115_);
lean_ctor_set(v_reuseFailAlloc_6145_, 8, v_snapshotTasks_6116_);
v___x_6124_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v_mctx_6127_; lean_object* v_zetaDeltaFVarIds_6128_; lean_object* v_postponed_6129_; lean_object* v_diag_6130_; lean_object* v___x_6132_; uint8_t v_isShared_6133_; uint8_t v_isSharedCheck_6143_; 
v___x_6125_ = lean_st_ref_set(v___y_6090_, v___x_6124_);
v___x_6126_ = lean_st_ref_take(v___y_6088_);
v_mctx_6127_ = lean_ctor_get(v___x_6126_, 0);
v_zetaDeltaFVarIds_6128_ = lean_ctor_get(v___x_6126_, 2);
v_postponed_6129_ = lean_ctor_get(v___x_6126_, 3);
v_diag_6130_ = lean_ctor_get(v___x_6126_, 4);
v_isSharedCheck_6143_ = !lean_is_exclusive(v___x_6126_);
if (v_isSharedCheck_6143_ == 0)
{
lean_object* v_unused_6144_; 
v_unused_6144_ = lean_ctor_get(v___x_6126_, 1);
lean_dec(v_unused_6144_);
v___x_6132_ = v___x_6126_;
v_isShared_6133_ = v_isSharedCheck_6143_;
goto v_resetjp_6131_;
}
else
{
lean_inc(v_diag_6130_);
lean_inc(v_postponed_6129_);
lean_inc(v_zetaDeltaFVarIds_6128_);
lean_inc(v_mctx_6127_);
lean_dec(v___x_6126_);
v___x_6132_ = lean_box(0);
v_isShared_6133_ = v_isSharedCheck_6143_;
goto v_resetjp_6131_;
}
v_resetjp_6131_:
{
lean_object* v___x_6134_; lean_object* v___x_6136_; 
v___x_6134_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__7_spec__8___redArg___closed__3);
if (v_isShared_6133_ == 0)
{
lean_ctor_set(v___x_6132_, 1, v___x_6134_);
v___x_6136_ = v___x_6132_;
goto v_reusejp_6135_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_mctx_6127_);
lean_ctor_set(v_reuseFailAlloc_6142_, 1, v___x_6134_);
lean_ctor_set(v_reuseFailAlloc_6142_, 2, v_zetaDeltaFVarIds_6128_);
lean_ctor_set(v_reuseFailAlloc_6142_, 3, v_postponed_6129_);
lean_ctor_set(v_reuseFailAlloc_6142_, 4, v_diag_6130_);
v___x_6136_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6135_;
}
v_reusejp_6135_:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6140_; 
v___x_6137_ = lean_st_ref_set(v___y_6088_, v___x_6136_);
v___x_6138_ = lean_box(0);
if (v_isShared_6107_ == 0)
{
lean_ctor_set(v___x_6106_, 0, v___x_6138_);
v___x_6140_ = v___x_6106_;
goto v_reusejp_6139_;
}
else
{
lean_object* v_reuseFailAlloc_6141_; 
v_reuseFailAlloc_6141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6141_, 0, v___x_6138_);
v___x_6140_ = v_reuseFailAlloc_6141_;
goto v_reusejp_6139_;
}
v_reusejp_6139_:
{
return v___x_6140_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_6094_);
return v___x_6103_;
}
}
else
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6157_; 
lean_dec(v_a_6084_);
lean_dec(v___x_6065_);
lean_dec(v_a_6064_);
lean_dec(v_enumName_6063_);
v_a_6150_ = lean_ctor_get(v___x_6091_, 0);
v_isSharedCheck_6157_ = !lean_is_exclusive(v___x_6091_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6152_ = v___x_6091_;
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6091_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6155_; 
if (v_isShared_6153_ == 0)
{
v___x_6155_ = v___x_6152_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
v___x_6155_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
return v___x_6155_;
}
}
}
}
}
else
{
lean_object* v_a_6198_; lean_object* v___x_6200_; uint8_t v_isShared_6201_; uint8_t v_isSharedCheck_6205_; 
lean_dec_ref(v___x_6079_);
lean_dec_ref(v_h_6068_);
lean_dec_ref(v___x_6067_);
lean_dec(v___x_6065_);
lean_dec(v_a_6064_);
lean_dec(v_enumName_6063_);
lean_dec_ref(v_b_6060_);
lean_dec_ref(v_x_6059_);
lean_dec_ref(v_P_6058_);
v_a_6198_ = lean_ctor_get(v___x_6083_, 0);
v_isSharedCheck_6205_ = !lean_is_exclusive(v___x_6083_);
if (v_isSharedCheck_6205_ == 0)
{
v___x_6200_ = v___x_6083_;
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
else
{
lean_inc(v_a_6198_);
lean_dec(v___x_6083_);
v___x_6200_ = lean_box(0);
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
v_resetjp_6199_:
{
lean_object* v___x_6203_; 
if (v_isShared_6201_ == 0)
{
v___x_6203_ = v___x_6200_;
goto v_reusejp_6202_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_a_6198_);
v___x_6203_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6202_;
}
v_reusejp_6202_:
{
return v___x_6203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed(lean_object* v_P_6206_, lean_object* v_x_6207_, lean_object* v_b_6208_, lean_object* v___x_6209_, lean_object* v___x_6210_, lean_object* v_enumName_6211_, lean_object* v_a_6212_, lean_object* v___x_6213_, lean_object* v_val_6214_, lean_object* v___x_6215_, lean_object* v_h_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_){
_start:
{
uint8_t v___x_4346__boxed_6222_; lean_object* v_res_6223_; 
v___x_4346__boxed_6222_ = lean_unbox(v___x_6210_);
v_res_6223_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1(v_P_6206_, v_x_6207_, v_b_6208_, v___x_6209_, v___x_4346__boxed_6222_, v_enumName_6211_, v_a_6212_, v___x_6213_, v_val_6214_, v___x_6215_, v_h_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_);
lean_dec(v___y_6220_);
lean_dec_ref(v___y_6219_);
lean_dec(v___y_6218_);
lean_dec_ref(v___y_6217_);
lean_dec_ref(v_val_6214_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(lean_object* v_x_6224_, lean_object* v_P_6225_, lean_object* v___x_6226_, uint8_t v___x_6227_, lean_object* v_enumName_6228_, lean_object* v_a_6229_, lean_object* v___x_6230_, lean_object* v_val_6231_, lean_object* v___x_6232_, lean_object* v_b_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
lean_object* v___x_6239_; 
lean_inc_ref(v_b_6233_);
lean_inc_ref(v_x_6224_);
v___x_6239_ = l_Lean_Meta_mkEq(v_x_6224_, v_b_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
if (lean_obj_tag(v___x_6239_) == 0)
{
lean_object* v_a_6240_; lean_object* v___x_6241_; lean_object* v___f_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v_a_6240_ = lean_ctor_get(v___x_6239_, 0);
lean_inc(v_a_6240_);
lean_dec_ref_known(v___x_6239_, 1);
v___x_6241_ = lean_box(v___x_6227_);
v___f_6242_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___boxed), 16, 10);
lean_closure_set(v___f_6242_, 0, v_P_6225_);
lean_closure_set(v___f_6242_, 1, v_x_6224_);
lean_closure_set(v___f_6242_, 2, v_b_6233_);
lean_closure_set(v___f_6242_, 3, v___x_6226_);
lean_closure_set(v___f_6242_, 4, v___x_6241_);
lean_closure_set(v___f_6242_, 5, v_enumName_6228_);
lean_closure_set(v___f_6242_, 6, v_a_6229_);
lean_closure_set(v___f_6242_, 7, v___x_6230_);
lean_closure_set(v___f_6242_, 8, v_val_6231_);
lean_closure_set(v___f_6242_, 9, v___x_6232_);
v___x_6243_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq___closed__13));
v___x_6244_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0___redArg(v___x_6243_, v_a_6240_, v___f_6242_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
return v___x_6244_;
}
else
{
lean_object* v_a_6245_; lean_object* v___x_6247_; uint8_t v_isShared_6248_; uint8_t v_isSharedCheck_6252_; 
lean_dec_ref(v_b_6233_);
lean_dec_ref(v___x_6232_);
lean_dec_ref(v_val_6231_);
lean_dec(v___x_6230_);
lean_dec(v_a_6229_);
lean_dec(v_enumName_6228_);
lean_dec_ref(v___x_6226_);
lean_dec_ref(v_P_6225_);
lean_dec_ref(v_x_6224_);
v_a_6245_ = lean_ctor_get(v___x_6239_, 0);
v_isSharedCheck_6252_ = !lean_is_exclusive(v___x_6239_);
if (v_isSharedCheck_6252_ == 0)
{
v___x_6247_ = v___x_6239_;
v_isShared_6248_ = v_isSharedCheck_6252_;
goto v_resetjp_6246_;
}
else
{
lean_inc(v_a_6245_);
lean_dec(v___x_6239_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed(lean_object* v_x_6253_, lean_object* v_P_6254_, lean_object* v___x_6255_, lean_object* v___x_6256_, lean_object* v_enumName_6257_, lean_object* v_a_6258_, lean_object* v___x_6259_, lean_object* v_val_6260_, lean_object* v___x_6261_, lean_object* v_b_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_){
_start:
{
uint8_t v___x_4646__boxed_6268_; lean_object* v_res_6269_; 
v___x_4646__boxed_6268_ = lean_unbox(v___x_6256_);
v_res_6269_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2(v_x_6253_, v_P_6254_, v___x_6255_, v___x_4646__boxed_6268_, v_enumName_6257_, v_a_6258_, v___x_6259_, v_val_6260_, v___x_6261_, v_b_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
return v_res_6269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(lean_object* v_P_6270_, lean_object* v_x_6271_, lean_object* v___x_6272_, lean_object* v_enumName_6273_, lean_object* v_a_6274_, lean_object* v___x_6275_, lean_object* v_val_6276_, lean_object* v___x_6277_, lean_object* v_name_6278_, uint8_t v_bi_6279_, lean_object* v_type_6280_, uint8_t v_kind_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_){
_start:
{
uint8_t v___x_6287_; lean_object* v___x_6288_; lean_object* v___f_6289_; lean_object* v___x_6290_; 
v___x_6287_ = 1;
v___x_6288_ = lean_box(v___x_6287_);
v___f_6289_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__2___boxed), 15, 9);
lean_closure_set(v___f_6289_, 0, v_x_6271_);
lean_closure_set(v___f_6289_, 1, v_P_6270_);
lean_closure_set(v___f_6289_, 2, v___x_6272_);
lean_closure_set(v___f_6289_, 3, v___x_6288_);
lean_closure_set(v___f_6289_, 4, v_enumName_6273_);
lean_closure_set(v___f_6289_, 5, v_a_6274_);
lean_closure_set(v___f_6289_, 6, v___x_6275_);
lean_closure_set(v___f_6289_, 7, v_val_6276_);
lean_closure_set(v___f_6289_, 8, v___x_6277_);
v___x_6290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6278_, v_bi_6279_, v_type_6280_, v___f_6289_, v_kind_6281_, v___y_6282_, v___y_6283_, v___y_6284_, v___y_6285_);
if (lean_obj_tag(v___x_6290_) == 0)
{
lean_object* v_a_6291_; lean_object* v___x_6293_; uint8_t v_isShared_6294_; uint8_t v_isSharedCheck_6298_; 
v_a_6291_ = lean_ctor_get(v___x_6290_, 0);
v_isSharedCheck_6298_ = !lean_is_exclusive(v___x_6290_);
if (v_isSharedCheck_6298_ == 0)
{
v___x_6293_ = v___x_6290_;
v_isShared_6294_ = v_isSharedCheck_6298_;
goto v_resetjp_6292_;
}
else
{
lean_inc(v_a_6291_);
lean_dec(v___x_6290_);
v___x_6293_ = lean_box(0);
v_isShared_6294_ = v_isSharedCheck_6298_;
goto v_resetjp_6292_;
}
v_resetjp_6292_:
{
lean_object* v___x_6296_; 
if (v_isShared_6294_ == 0)
{
v___x_6296_ = v___x_6293_;
goto v_reusejp_6295_;
}
else
{
lean_object* v_reuseFailAlloc_6297_; 
v_reuseFailAlloc_6297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6297_, 0, v_a_6291_);
v___x_6296_ = v_reuseFailAlloc_6297_;
goto v_reusejp_6295_;
}
v_reusejp_6295_:
{
return v___x_6296_;
}
}
}
else
{
lean_object* v_a_6299_; lean_object* v___x_6301_; uint8_t v_isShared_6302_; uint8_t v_isSharedCheck_6306_; 
v_a_6299_ = lean_ctor_get(v___x_6290_, 0);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6290_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6301_ = v___x_6290_;
v_isShared_6302_ = v_isSharedCheck_6306_;
goto v_resetjp_6300_;
}
else
{
lean_inc(v_a_6299_);
lean_dec(v___x_6290_);
v___x_6301_ = lean_box(0);
v_isShared_6302_ = v_isSharedCheck_6306_;
goto v_resetjp_6300_;
}
v_resetjp_6300_:
{
lean_object* v___x_6304_; 
if (v_isShared_6302_ == 0)
{
v___x_6304_ = v___x_6301_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v_a_6299_);
v___x_6304_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
return v___x_6304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___boxed(lean_object** _args){
lean_object* v_P_6307_ = _args[0];
lean_object* v_x_6308_ = _args[1];
lean_object* v___x_6309_ = _args[2];
lean_object* v_enumName_6310_ = _args[3];
lean_object* v_a_6311_ = _args[4];
lean_object* v___x_6312_ = _args[5];
lean_object* v_val_6313_ = _args[6];
lean_object* v___x_6314_ = _args[7];
lean_object* v_name_6315_ = _args[8];
lean_object* v_bi_6316_ = _args[9];
lean_object* v_type_6317_ = _args[10];
lean_object* v_kind_6318_ = _args[11];
lean_object* v___y_6319_ = _args[12];
lean_object* v___y_6320_ = _args[13];
lean_object* v___y_6321_ = _args[14];
lean_object* v___y_6322_ = _args[15];
lean_object* v___y_6323_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6324_; uint8_t v_kind_boxed_6325_; lean_object* v_res_6326_; 
v_bi_boxed_6324_ = lean_unbox(v_bi_6316_);
v_kind_boxed_6325_ = lean_unbox(v_kind_6318_);
v_res_6326_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6307_, v_x_6308_, v___x_6309_, v_enumName_6310_, v_a_6311_, v___x_6312_, v_val_6313_, v___x_6314_, v_name_6315_, v_bi_boxed_6324_, v_type_6317_, v_kind_boxed_6325_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
lean_dec(v___y_6322_);
lean_dec_ref(v___y_6321_);
lean_dec(v___y_6320_);
lean_dec_ref(v___y_6319_);
return v_res_6326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(lean_object* v_P_6327_, lean_object* v___x_6328_, lean_object* v_enumName_6329_, lean_object* v_a_6330_, lean_object* v___x_6331_, lean_object* v_val_6332_, lean_object* v___x_6333_, uint8_t v___x_6334_, lean_object* v___x_6335_, lean_object* v_b_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
lean_object* v___x_6342_; uint8_t v___x_6343_; lean_object* v___x_6344_; 
v___x_6342_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__1___closed__1));
v___x_6343_ = 0;
v___x_6344_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0(v_P_6327_, v_b_6336_, v___x_6328_, v_enumName_6329_, v_a_6330_, v___x_6331_, v_val_6332_, v___x_6333_, v___x_6342_, v___x_6334_, v___x_6335_, v___x_6343_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_);
return v___x_6344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed(lean_object* v_P_6345_, lean_object* v___x_6346_, lean_object* v_enumName_6347_, lean_object* v_a_6348_, lean_object* v___x_6349_, lean_object* v_val_6350_, lean_object* v___x_6351_, lean_object* v___x_6352_, lean_object* v___x_6353_, lean_object* v_b_6354_, lean_object* v___y_6355_, lean_object* v___y_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_){
_start:
{
uint8_t v___x_4785__boxed_6360_; lean_object* v_res_6361_; 
v___x_4785__boxed_6360_ = lean_unbox(v___x_6352_);
v_res_6361_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0(v_P_6345_, v___x_6346_, v_enumName_6347_, v_a_6348_, v___x_6349_, v_val_6350_, v___x_6351_, v___x_4785__boxed_6360_, v___x_6353_, v_b_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_);
lean_dec(v___y_6358_);
lean_dec_ref(v___y_6357_);
lean_dec(v___y_6356_);
lean_dec_ref(v___y_6355_);
return v_res_6361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(lean_object* v_P_6362_, lean_object* v___x_6363_, lean_object* v_enumName_6364_, lean_object* v_a_6365_, lean_object* v___x_6366_, lean_object* v_val_6367_, lean_object* v___x_6368_, lean_object* v___x_6369_, lean_object* v_name_6370_, uint8_t v_bi_6371_, lean_object* v_type_6372_, uint8_t v_kind_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_){
_start:
{
uint8_t v___x_6379_; lean_object* v___x_6380_; lean_object* v___f_6381_; lean_object* v___x_6382_; 
v___x_6379_ = 1;
v___x_6380_ = lean_box(v___x_6379_);
v___f_6381_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___lam__0___boxed), 15, 9);
lean_closure_set(v___f_6381_, 0, v_P_6362_);
lean_closure_set(v___f_6381_, 1, v___x_6363_);
lean_closure_set(v___f_6381_, 2, v_enumName_6364_);
lean_closure_set(v___f_6381_, 3, v_a_6365_);
lean_closure_set(v___f_6381_, 4, v___x_6366_);
lean_closure_set(v___f_6381_, 5, v_val_6367_);
lean_closure_set(v___f_6381_, 6, v___x_6368_);
lean_closure_set(v___f_6381_, 7, v___x_6380_);
lean_closure_set(v___f_6381_, 8, v___x_6369_);
v___x_6382_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6370_, v_bi_6371_, v_type_6372_, v___f_6381_, v_kind_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_);
if (lean_obj_tag(v___x_6382_) == 0)
{
lean_object* v_a_6383_; lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6390_; 
v_a_6383_ = lean_ctor_get(v___x_6382_, 0);
v_isSharedCheck_6390_ = !lean_is_exclusive(v___x_6382_);
if (v_isSharedCheck_6390_ == 0)
{
v___x_6385_ = v___x_6382_;
v_isShared_6386_ = v_isSharedCheck_6390_;
goto v_resetjp_6384_;
}
else
{
lean_inc(v_a_6383_);
lean_dec(v___x_6382_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6390_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v___x_6388_; 
if (v_isShared_6386_ == 0)
{
v___x_6388_ = v___x_6385_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6389_; 
v_reuseFailAlloc_6389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6389_, 0, v_a_6383_);
v___x_6388_ = v_reuseFailAlloc_6389_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
return v___x_6388_;
}
}
}
else
{
lean_object* v_a_6391_; lean_object* v___x_6393_; uint8_t v_isShared_6394_; uint8_t v_isSharedCheck_6398_; 
v_a_6391_ = lean_ctor_get(v___x_6382_, 0);
v_isSharedCheck_6398_ = !lean_is_exclusive(v___x_6382_);
if (v_isSharedCheck_6398_ == 0)
{
v___x_6393_ = v___x_6382_;
v_isShared_6394_ = v_isSharedCheck_6398_;
goto v_resetjp_6392_;
}
else
{
lean_inc(v_a_6391_);
lean_dec(v___x_6382_);
v___x_6393_ = lean_box(0);
v_isShared_6394_ = v_isSharedCheck_6398_;
goto v_resetjp_6392_;
}
v_resetjp_6392_:
{
lean_object* v___x_6396_; 
if (v_isShared_6394_ == 0)
{
v___x_6396_ = v___x_6393_;
goto v_reusejp_6395_;
}
else
{
lean_object* v_reuseFailAlloc_6397_; 
v_reuseFailAlloc_6397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_a_6391_);
v___x_6396_ = v_reuseFailAlloc_6397_;
goto v_reusejp_6395_;
}
v_reusejp_6395_:
{
return v___x_6396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1___boxed(lean_object** _args){
lean_object* v_P_6399_ = _args[0];
lean_object* v___x_6400_ = _args[1];
lean_object* v_enumName_6401_ = _args[2];
lean_object* v_a_6402_ = _args[3];
lean_object* v___x_6403_ = _args[4];
lean_object* v_val_6404_ = _args[5];
lean_object* v___x_6405_ = _args[6];
lean_object* v___x_6406_ = _args[7];
lean_object* v_name_6407_ = _args[8];
lean_object* v_bi_6408_ = _args[9];
lean_object* v_type_6409_ = _args[10];
lean_object* v_kind_6410_ = _args[11];
lean_object* v___y_6411_ = _args[12];
lean_object* v___y_6412_ = _args[13];
lean_object* v___y_6413_ = _args[14];
lean_object* v___y_6414_ = _args[15];
lean_object* v___y_6415_ = _args[16];
_start:
{
uint8_t v_bi_boxed_6416_; uint8_t v_kind_boxed_6417_; lean_object* v_res_6418_; 
v_bi_boxed_6416_ = lean_unbox(v_bi_6408_);
v_kind_boxed_6417_ = lean_unbox(v_kind_6410_);
v_res_6418_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_P_6399_, v___x_6400_, v_enumName_6401_, v_a_6402_, v___x_6403_, v_val_6404_, v___x_6405_, v___x_6406_, v_name_6407_, v_bi_boxed_6416_, v_type_6409_, v_kind_boxed_6417_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
lean_dec(v___y_6414_);
lean_dec_ref(v___y_6413_);
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
return v_res_6418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(lean_object* v___x_6419_, lean_object* v_enumName_6420_, lean_object* v_a_6421_, lean_object* v___x_6422_, lean_object* v_val_6423_, lean_object* v___x_6424_, lean_object* v___x_6425_, uint8_t v___x_6426_, lean_object* v_b_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_){
_start:
{
lean_object* v___x_6433_; uint8_t v___x_6434_; lean_object* v___x_6435_; 
v___x_6433_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___lam__2___closed__1));
v___x_6434_ = 0;
lean_inc_ref(v___x_6425_);
v___x_6435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__1(v_b_6427_, v___x_6419_, v_enumName_6420_, v_a_6421_, v___x_6422_, v_val_6423_, v___x_6424_, v___x_6425_, v___x_6433_, v___x_6426_, v___x_6425_, v___x_6434_, v___y_6428_, v___y_6429_, v___y_6430_, v___y_6431_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed(lean_object* v___x_6436_, lean_object* v_enumName_6437_, lean_object* v_a_6438_, lean_object* v___x_6439_, lean_object* v_val_6440_, lean_object* v___x_6441_, lean_object* v___x_6442_, lean_object* v___x_6443_, lean_object* v_b_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_){
_start:
{
uint8_t v___x_4905__boxed_6450_; lean_object* v_res_6451_; 
v___x_4905__boxed_6450_ = lean_unbox(v___x_6443_);
v_res_6451_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0(v___x_6436_, v_enumName_6437_, v_a_6438_, v___x_6439_, v_val_6440_, v___x_6441_, v___x_6442_, v___x_4905__boxed_6450_, v_b_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec(v___y_6448_);
lean_dec_ref(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec_ref(v___y_6445_);
return v_res_6451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(lean_object* v___x_6452_, lean_object* v_enumName_6453_, lean_object* v_a_6454_, lean_object* v___x_6455_, lean_object* v_val_6456_, lean_object* v___x_6457_, lean_object* v___x_6458_, lean_object* v_name_6459_, uint8_t v_bi_6460_, lean_object* v_type_6461_, uint8_t v_kind_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_){
_start:
{
uint8_t v___x_6468_; lean_object* v___x_6469_; lean_object* v___f_6470_; lean_object* v___x_6471_; 
v___x_6468_ = 1;
v___x_6469_ = lean_box(v___x_6468_);
v___f_6470_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___lam__0___boxed), 14, 8);
lean_closure_set(v___f_6470_, 0, v___x_6452_);
lean_closure_set(v___f_6470_, 1, v_enumName_6453_);
lean_closure_set(v___f_6470_, 2, v_a_6454_);
lean_closure_set(v___f_6470_, 3, v___x_6455_);
lean_closure_set(v___f_6470_, 4, v_val_6456_);
lean_closure_set(v___f_6470_, 5, v___x_6457_);
lean_closure_set(v___f_6470_, 6, v___x_6458_);
lean_closure_set(v___f_6470_, 7, v___x_6469_);
v___x_6471_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_6459_, v_bi_6460_, v_type_6461_, v___f_6470_, v_kind_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
if (lean_obj_tag(v___x_6471_) == 0)
{
lean_object* v_a_6472_; lean_object* v___x_6474_; uint8_t v_isShared_6475_; uint8_t v_isSharedCheck_6479_; 
v_a_6472_ = lean_ctor_get(v___x_6471_, 0);
v_isSharedCheck_6479_ = !lean_is_exclusive(v___x_6471_);
if (v_isSharedCheck_6479_ == 0)
{
v___x_6474_ = v___x_6471_;
v_isShared_6475_ = v_isSharedCheck_6479_;
goto v_resetjp_6473_;
}
else
{
lean_inc(v_a_6472_);
lean_dec(v___x_6471_);
v___x_6474_ = lean_box(0);
v_isShared_6475_ = v_isSharedCheck_6479_;
goto v_resetjp_6473_;
}
v_resetjp_6473_:
{
lean_object* v___x_6477_; 
if (v_isShared_6475_ == 0)
{
v___x_6477_ = v___x_6474_;
goto v_reusejp_6476_;
}
else
{
lean_object* v_reuseFailAlloc_6478_; 
v_reuseFailAlloc_6478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6478_, 0, v_a_6472_);
v___x_6477_ = v_reuseFailAlloc_6478_;
goto v_reusejp_6476_;
}
v_reusejp_6476_:
{
return v___x_6477_;
}
}
}
else
{
lean_object* v_a_6480_; lean_object* v___x_6482_; uint8_t v_isShared_6483_; uint8_t v_isSharedCheck_6487_; 
v_a_6480_ = lean_ctor_get(v___x_6471_, 0);
v_isSharedCheck_6487_ = !lean_is_exclusive(v___x_6471_);
if (v_isSharedCheck_6487_ == 0)
{
v___x_6482_ = v___x_6471_;
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
else
{
lean_inc(v_a_6480_);
lean_dec(v___x_6471_);
v___x_6482_ = lean_box(0);
v_isShared_6483_ = v_isSharedCheck_6487_;
goto v_resetjp_6481_;
}
v_resetjp_6481_:
{
lean_object* v___x_6485_; 
if (v_isShared_6483_ == 0)
{
v___x_6485_ = v___x_6482_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6486_; 
v_reuseFailAlloc_6486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6486_, 0, v_a_6480_);
v___x_6485_ = v_reuseFailAlloc_6486_;
goto v_reusejp_6484_;
}
v_reusejp_6484_:
{
return v___x_6485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2___boxed(lean_object* v___x_6488_, lean_object* v_enumName_6489_, lean_object* v_a_6490_, lean_object* v___x_6491_, lean_object* v_val_6492_, lean_object* v___x_6493_, lean_object* v___x_6494_, lean_object* v_name_6495_, lean_object* v_bi_6496_, lean_object* v_type_6497_, lean_object* v_kind_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
uint8_t v_bi_boxed_6504_; uint8_t v_kind_boxed_6505_; lean_object* v_res_6506_; 
v_bi_boxed_6504_ = lean_unbox(v_bi_6496_);
v_kind_boxed_6505_ = lean_unbox(v_kind_6498_);
v_res_6506_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6488_, v_enumName_6489_, v_a_6490_, v___x_6491_, v_val_6492_, v___x_6493_, v___x_6494_, v_name_6495_, v_bi_boxed_6504_, v_type_6497_, v_kind_boxed_6505_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_);
lean_dec(v___y_6502_);
lean_dec_ref(v___y_6501_);
lean_dec(v___y_6500_);
lean_dec_ref(v___y_6499_);
return v_res_6506_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1(void){
_start:
{
lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; 
v___x_6508_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0___closed__6));
v___x_6509_ = lean_unsigned_to_nat(63u);
v___x_6510_ = lean_unsigned_to_nat(403u);
v___x_6511_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__0));
v___x_6512_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__2));
v___x_6513_ = l_mkPanicMessageWithDecl(v___x_6512_, v___x_6511_, v___x_6510_, v___x_6509_, v___x_6508_);
return v___x_6513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(lean_object* v_enumName_6514_, lean_object* v_a_6515_, lean_object* v_a_6516_, lean_object* v_a_6517_, lean_object* v_a_6518_){
_start:
{
lean_object* v___x_6520_; 
lean_inc(v_enumName_6514_);
v___x_6520_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_enumName_6514_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_);
if (lean_obj_tag(v___x_6520_) == 0)
{
lean_object* v_a_6521_; 
v_a_6521_ = lean_ctor_get(v___x_6520_, 0);
lean_inc(v_a_6521_);
lean_dec_ref_known(v___x_6520_, 1);
if (lean_obj_tag(v_a_6521_) == 5)
{
lean_object* v_val_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v_val_6522_ = lean_ctor_get(v_a_6521_, 0);
lean_inc_ref(v_val_6522_);
lean_dec_ref_known(v_a_6521_, 1);
v___x_6523_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType___closed__1));
v___x_6524_ = l_Lean_Core_mkFreshUserName(v___x_6523_, v_a_6517_, v_a_6518_);
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_object* v_toConstantVal_6525_; lean_object* v_a_6526_; lean_object* v_levelParams_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; uint8_t v___x_6540_; uint8_t v___x_6541_; lean_object* v___x_6542_; 
v_toConstantVal_6525_ = lean_ctor_get(v_val_6522_, 0);
v_a_6526_ = lean_ctor_get(v___x_6524_, 0);
lean_inc_n(v_a_6526_, 2);
lean_dec_ref_known(v___x_6524_, 1);
v_levelParams_6527_ = lean_ctor_get(v_toConstantVal_6525_, 1);
lean_inc_n(v_levelParams_6527_, 2);
v___x_6528_ = lean_box(0);
v___x_6529_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__2(v_levelParams_6527_, v___x_6528_);
lean_inc_n(v___x_6529_, 2);
lean_inc_n(v_enumName_6514_, 3);
v___x_6530_ = l_Lean_mkConst(v_enumName_6514_, v___x_6529_);
v___x_6531_ = l_Lean_mkLevelParam(v_a_6526_);
lean_inc(v___x_6531_);
v___x_6532_ = l_Lean_mkSort(v___x_6531_);
v___x_6533_ = l_mkCtorIdxName(v_enumName_6514_);
v___x_6534_ = l_Lean_mkConst(v___x_6533_, v___x_6529_);
v___x_6535_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionTypeName___closed__0));
v___x_6536_ = l_Lean_Name_str___override(v_enumName_6514_, v___x_6535_);
v___x_6537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6537_, 0, v___x_6531_);
lean_ctor_set(v___x_6537_, 1, v___x_6529_);
v___x_6538_ = l_Lean_mkConst(v___x_6536_, v___x_6537_);
v___x_6539_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType___closed__1));
v___x_6540_ = 1;
v___x_6541_ = 0;
v___x_6542_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__2(v___x_6538_, v_enumName_6514_, v_a_6526_, v_levelParams_6527_, v_val_6522_, v___x_6534_, v___x_6530_, v___x_6539_, v___x_6540_, v___x_6532_, v___x_6541_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_);
return v___x_6542_;
}
else
{
lean_object* v_a_6543_; lean_object* v___x_6545_; uint8_t v_isShared_6546_; uint8_t v_isSharedCheck_6550_; 
lean_dec_ref(v_val_6522_);
lean_dec(v_enumName_6514_);
v_a_6543_ = lean_ctor_get(v___x_6524_, 0);
v_isSharedCheck_6550_ = !lean_is_exclusive(v___x_6524_);
if (v_isSharedCheck_6550_ == 0)
{
v___x_6545_ = v___x_6524_;
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
else
{
lean_inc(v_a_6543_);
lean_dec(v___x_6524_);
v___x_6545_ = lean_box(0);
v_isShared_6546_ = v_isSharedCheck_6550_;
goto v_resetjp_6544_;
}
v_resetjp_6544_:
{
lean_object* v___x_6548_; 
if (v_isShared_6546_ == 0)
{
v___x_6548_ = v___x_6545_;
goto v_reusejp_6547_;
}
else
{
lean_object* v_reuseFailAlloc_6549_; 
v_reuseFailAlloc_6549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6549_, 0, v_a_6543_);
v___x_6548_ = v_reuseFailAlloc_6549_;
goto v_reusejp_6547_;
}
v_reusejp_6547_:
{
return v___x_6548_;
}
}
}
}
else
{
lean_object* v___x_6551_; lean_object* v___x_6552_; 
lean_dec(v_a_6521_);
lean_dec(v_enumName_6514_);
v___x_6551_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___closed__1);
v___x_6552_ = l_panic___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__8(v___x_6551_, v_a_6515_, v_a_6516_, v_a_6517_, v_a_6518_);
return v___x_6552_;
}
}
else
{
lean_object* v_a_6553_; lean_object* v___x_6555_; uint8_t v_isShared_6556_; uint8_t v_isSharedCheck_6560_; 
lean_dec(v_enumName_6514_);
v_a_6553_ = lean_ctor_get(v___x_6520_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6560_ == 0)
{
v___x_6555_ = v___x_6520_;
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
else
{
lean_inc(v_a_6553_);
lean_dec(v___x_6520_);
v___x_6555_ = lean_box(0);
v_isShared_6556_ = v_isSharedCheck_6560_;
goto v_resetjp_6554_;
}
v_resetjp_6554_:
{
lean_object* v___x_6558_; 
if (v_isShared_6556_ == 0)
{
v___x_6558_ = v___x_6555_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6559_; 
v_reuseFailAlloc_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
v___x_6558_ = v_reuseFailAlloc_6559_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
return v___x_6558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion___boxed(lean_object* v_enumName_6561_, lean_object* v_a_6562_, lean_object* v_a_6563_, lean_object* v_a_6564_, lean_object* v_a_6565_, lean_object* v_a_6566_){
_start:
{
lean_object* v_res_6567_; 
v_res_6567_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6561_, v_a_6562_, v_a_6563_, v_a_6564_, v_a_6565_);
lean_dec(v_a_6565_);
lean_dec_ref(v_a_6564_);
lean_dec(v_a_6563_);
lean_dec_ref(v_a_6562_);
return v_res_6567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(lean_object* v_enumName_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_){
_start:
{
lean_object* v___x_6574_; lean_object* v_env_6575_; lean_object* v___x_6576_; uint8_t v___x_6577_; uint8_t v___x_6578_; 
v___x_6574_ = lean_st_ref_get(v_a_6572_);
v_env_6575_ = lean_ctor_get(v___x_6574_, 0);
lean_inc_ref(v_env_6575_);
lean_dec(v___x_6574_);
v___x_6576_ = ((lean_object*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkIfNatEq_spec__0_spec__0___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion_spec__0___lam__1___closed__2));
v___x_6577_ = 1;
v___x_6578_ = l_Lean_Environment_contains(v_env_6575_, v___x_6576_, v___x_6577_);
if (v___x_6578_ == 0)
{
lean_object* v___x_6579_; 
v___x_6579_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_enumName_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
return v___x_6579_;
}
else
{
lean_object* v___x_6580_; 
lean_inc(v_enumName_6568_);
v___x_6580_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusionType(v_enumName_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
if (lean_obj_tag(v___x_6580_) == 0)
{
lean_object* v___x_6581_; 
lean_dec_ref_known(v___x_6580_, 1);
v___x_6581_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum_mkNoConfusion(v_enumName_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
return v___x_6581_;
}
else
{
lean_dec(v_enumName_6568_);
return v___x_6580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum___boxed(lean_object* v_enumName_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_){
_start:
{
lean_object* v_res_6588_; 
v_res_6588_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_enumName_6582_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_);
lean_dec(v_a_6586_);
lean_dec_ref(v_a_6585_);
lean_dec(v_a_6584_);
lean_dec_ref(v_a_6583_);
return v_res_6588_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; 
v___x_6589_ = lean_unsigned_to_nat(32u);
v___x_6590_ = lean_mk_empty_array_with_capacity(v___x_6589_);
v___x_6591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6591_, 0, v___x_6590_);
return v___x_6591_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; 
v___x_6592_ = ((size_t)5ULL);
v___x_6593_ = lean_unsigned_to_nat(0u);
v___x_6594_ = lean_unsigned_to_nat(32u);
v___x_6595_ = lean_mk_empty_array_with_capacity(v___x_6594_);
v___x_6596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__0);
v___x_6597_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6597_, 0, v___x_6596_);
lean_ctor_set(v___x_6597_, 1, v___x_6595_);
lean_ctor_set(v___x_6597_, 2, v___x_6593_);
lean_ctor_set(v___x_6597_, 3, v___x_6593_);
lean_ctor_set_usize(v___x_6597_, 4, v___x_6592_);
return v___x_6597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(lean_object* v___y_6598_){
_start:
{
lean_object* v___x_6600_; lean_object* v_traceState_6601_; lean_object* v_traces_6602_; lean_object* v___x_6603_; lean_object* v_traceState_6604_; lean_object* v_env_6605_; lean_object* v_nextMacroScope_6606_; lean_object* v_ngen_6607_; lean_object* v_auxDeclNGen_6608_; lean_object* v_cache_6609_; lean_object* v_messages_6610_; lean_object* v_infoState_6611_; lean_object* v_snapshotTasks_6612_; lean_object* v___x_6614_; uint8_t v_isShared_6615_; uint8_t v_isSharedCheck_6631_; 
v___x_6600_ = lean_st_ref_get(v___y_6598_);
v_traceState_6601_ = lean_ctor_get(v___x_6600_, 4);
lean_inc_ref(v_traceState_6601_);
lean_dec(v___x_6600_);
v_traces_6602_ = lean_ctor_get(v_traceState_6601_, 0);
lean_inc_ref(v_traces_6602_);
lean_dec_ref(v_traceState_6601_);
v___x_6603_ = lean_st_ref_take(v___y_6598_);
v_traceState_6604_ = lean_ctor_get(v___x_6603_, 4);
v_env_6605_ = lean_ctor_get(v___x_6603_, 0);
v_nextMacroScope_6606_ = lean_ctor_get(v___x_6603_, 1);
v_ngen_6607_ = lean_ctor_get(v___x_6603_, 2);
v_auxDeclNGen_6608_ = lean_ctor_get(v___x_6603_, 3);
v_cache_6609_ = lean_ctor_get(v___x_6603_, 5);
v_messages_6610_ = lean_ctor_get(v___x_6603_, 6);
v_infoState_6611_ = lean_ctor_get(v___x_6603_, 7);
v_snapshotTasks_6612_ = lean_ctor_get(v___x_6603_, 8);
v_isSharedCheck_6631_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6631_ == 0)
{
v___x_6614_ = v___x_6603_;
v_isShared_6615_ = v_isSharedCheck_6631_;
goto v_resetjp_6613_;
}
else
{
lean_inc(v_snapshotTasks_6612_);
lean_inc(v_infoState_6611_);
lean_inc(v_messages_6610_);
lean_inc(v_cache_6609_);
lean_inc(v_traceState_6604_);
lean_inc(v_auxDeclNGen_6608_);
lean_inc(v_ngen_6607_);
lean_inc(v_nextMacroScope_6606_);
lean_inc(v_env_6605_);
lean_dec(v___x_6603_);
v___x_6614_ = lean_box(0);
v_isShared_6615_ = v_isSharedCheck_6631_;
goto v_resetjp_6613_;
}
v_resetjp_6613_:
{
uint64_t v_tid_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6629_; 
v_tid_6616_ = lean_ctor_get_uint64(v_traceState_6604_, sizeof(void*)*1);
v_isSharedCheck_6629_ = !lean_is_exclusive(v_traceState_6604_);
if (v_isSharedCheck_6629_ == 0)
{
lean_object* v_unused_6630_; 
v_unused_6630_ = lean_ctor_get(v_traceState_6604_, 0);
lean_dec(v_unused_6630_);
v___x_6618_ = v_traceState_6604_;
v_isShared_6619_ = v_isSharedCheck_6629_;
goto v_resetjp_6617_;
}
else
{
lean_dec(v_traceState_6604_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6629_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6620_; lean_object* v___x_6622_; 
v___x_6620_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___closed__1);
if (v_isShared_6619_ == 0)
{
lean_ctor_set(v___x_6618_, 0, v___x_6620_);
v___x_6622_ = v___x_6618_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6628_; 
v_reuseFailAlloc_6628_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6628_, 0, v___x_6620_);
lean_ctor_set_uint64(v_reuseFailAlloc_6628_, sizeof(void*)*1, v_tid_6616_);
v___x_6622_ = v_reuseFailAlloc_6628_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
lean_object* v___x_6624_; 
if (v_isShared_6615_ == 0)
{
lean_ctor_set(v___x_6614_, 4, v___x_6622_);
v___x_6624_ = v___x_6614_;
goto v_reusejp_6623_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v_env_6605_);
lean_ctor_set(v_reuseFailAlloc_6627_, 1, v_nextMacroScope_6606_);
lean_ctor_set(v_reuseFailAlloc_6627_, 2, v_ngen_6607_);
lean_ctor_set(v_reuseFailAlloc_6627_, 3, v_auxDeclNGen_6608_);
lean_ctor_set(v_reuseFailAlloc_6627_, 4, v___x_6622_);
lean_ctor_set(v_reuseFailAlloc_6627_, 5, v_cache_6609_);
lean_ctor_set(v_reuseFailAlloc_6627_, 6, v_messages_6610_);
lean_ctor_set(v_reuseFailAlloc_6627_, 7, v_infoState_6611_);
lean_ctor_set(v_reuseFailAlloc_6627_, 8, v_snapshotTasks_6612_);
v___x_6624_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6623_;
}
v_reusejp_6623_:
{
lean_object* v___x_6625_; lean_object* v___x_6626_; 
v___x_6625_ = lean_st_ref_set(v___y_6598_, v___x_6624_);
v___x_6626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6626_, 0, v_traces_6602_);
return v___x_6626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg___boxed(lean_object* v___y_6632_, lean_object* v___y_6633_){
_start:
{
lean_object* v_res_6634_; 
v_res_6634_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6632_);
lean_dec(v___y_6632_);
return v_res_6634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_){
_start:
{
lean_object* v___x_6640_; 
v___x_6640_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v___y_6638_);
return v___x_6640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___boxed(lean_object* v___y_6641_, lean_object* v___y_6642_, lean_object* v___y_6643_, lean_object* v___y_6644_, lean_object* v___y_6645_){
_start:
{
lean_object* v_res_6646_; 
v_res_6646_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1(v___y_6641_, v___y_6642_, v___y_6643_, v___y_6644_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec(v___y_6642_);
lean_dec_ref(v___y_6641_);
return v_res_6646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0(lean_object* v_declName_6647_, lean_object* v_x_6648_, lean_object* v___y_6649_, lean_object* v___y_6650_, lean_object* v___y_6651_, lean_object* v___y_6652_){
_start:
{
lean_object* v___x_6654_; lean_object* v___x_6655_; 
v___x_6654_ = l_Lean_MessageData_ofName(v_declName_6647_);
v___x_6655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6655_, 0, v___x_6654_);
return v___x_6655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___lam__0___boxed(lean_object* v_declName_6656_, lean_object* v_x_6657_, lean_object* v___y_6658_, lean_object* v___y_6659_, lean_object* v___y_6660_, lean_object* v___y_6661_, lean_object* v___y_6662_){
_start:
{
lean_object* v_res_6663_; 
v_res_6663_ = l_Lean_mkNoConfusion___lam__0(v_declName_6656_, v_x_6657_, v___y_6658_, v___y_6659_, v___y_6660_, v___y_6661_);
lean_dec(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6659_);
lean_dec_ref(v___y_6658_);
lean_dec_ref(v_x_6657_);
return v_res_6663_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(uint8_t v___x_6664_, lean_object* v_x_6665_, lean_object* v___y_6666_, lean_object* v___y_6667_, lean_object* v___y_6668_, lean_object* v___y_6669_){
_start:
{
if (lean_obj_tag(v_x_6665_) == 0)
{
uint8_t v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; 
v___x_6671_ = 1;
v___x_6672_ = lean_box(v___x_6671_);
v___x_6673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6673_, 0, v___x_6672_);
return v___x_6673_;
}
else
{
lean_object* v_head_6674_; lean_object* v_tail_6675_; lean_object* v___x_6676_; 
v_head_6674_ = lean_ctor_get(v_x_6665_, 0);
lean_inc(v_head_6674_);
v_tail_6675_ = lean_ctor_get(v_x_6665_, 1);
lean_inc(v_tail_6675_);
lean_dec_ref_known(v_x_6665_, 2);
v___x_6676_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_head_6674_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_);
if (lean_obj_tag(v___x_6676_) == 0)
{
lean_object* v_a_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6697_; 
v_a_6677_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6697_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6697_ == 0)
{
v___x_6679_ = v___x_6676_;
v_isShared_6680_ = v_isSharedCheck_6697_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_a_6677_);
lean_dec(v___x_6676_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6697_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___y_6682_; uint8_t v_a_6683_; 
if (lean_obj_tag(v_a_6677_) == 6)
{
lean_object* v_val_6685_; lean_object* v_numFields_6686_; lean_object* v___x_6687_; uint8_t v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6691_; 
v_val_6685_ = lean_ctor_get(v_a_6677_, 0);
lean_inc_ref(v_val_6685_);
lean_dec_ref_known(v_a_6677_, 1);
v_numFields_6686_ = lean_ctor_get(v_val_6685_, 4);
lean_inc(v_numFields_6686_);
lean_dec_ref(v_val_6685_);
v___x_6687_ = lean_unsigned_to_nat(0u);
v___x_6688_ = lean_nat_dec_eq(v_numFields_6686_, v___x_6687_);
lean_dec(v_numFields_6686_);
v___x_6689_ = lean_box(v___x_6688_);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6689_);
v___x_6691_ = v___x_6679_;
goto v_reusejp_6690_;
}
else
{
lean_object* v_reuseFailAlloc_6692_; 
v_reuseFailAlloc_6692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6692_, 0, v___x_6689_);
v___x_6691_ = v_reuseFailAlloc_6692_;
goto v_reusejp_6690_;
}
v_reusejp_6690_:
{
v___y_6682_ = v___x_6691_;
v_a_6683_ = v___x_6688_;
goto v___jp_6681_;
}
}
else
{
lean_object* v___x_6693_; lean_object* v___x_6695_; 
lean_dec(v_a_6677_);
v___x_6693_ = lean_box(v___x_6664_);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6693_);
v___x_6695_ = v___x_6679_;
goto v_reusejp_6694_;
}
else
{
lean_object* v_reuseFailAlloc_6696_; 
v_reuseFailAlloc_6696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6696_, 0, v___x_6693_);
v___x_6695_ = v_reuseFailAlloc_6696_;
goto v_reusejp_6694_;
}
v_reusejp_6694_:
{
v___y_6682_ = v___x_6695_;
v_a_6683_ = v___x_6664_;
goto v___jp_6681_;
}
}
v___jp_6681_:
{
if (v_a_6683_ == 0)
{
lean_dec(v_tail_6675_);
return v___y_6682_;
}
else
{
lean_dec_ref(v___y_6682_);
v_x_6665_ = v_tail_6675_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_6698_; lean_object* v___x_6700_; uint8_t v_isShared_6701_; uint8_t v_isSharedCheck_6705_; 
lean_dec(v_tail_6675_);
v_a_6698_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6705_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6705_ == 0)
{
v___x_6700_ = v___x_6676_;
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
else
{
lean_inc(v_a_6698_);
lean_dec(v___x_6676_);
v___x_6700_ = lean_box(0);
v_isShared_6701_ = v_isSharedCheck_6705_;
goto v_resetjp_6699_;
}
v_resetjp_6699_:
{
lean_object* v___x_6703_; 
if (v_isShared_6701_ == 0)
{
v___x_6703_ = v___x_6700_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6704_; 
v_reuseFailAlloc_6704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_a_6698_);
v___x_6703_ = v_reuseFailAlloc_6704_;
goto v_reusejp_6702_;
}
v_reusejp_6702_:
{
return v___x_6703_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0___boxed(lean_object* v___x_6706_, lean_object* v_x_6707_, lean_object* v___y_6708_, lean_object* v___y_6709_, lean_object* v___y_6710_, lean_object* v___y_6711_, lean_object* v___y_6712_){
_start:
{
uint8_t v___x_8571__boxed_6713_; lean_object* v_res_6714_; 
v___x_8571__boxed_6713_ = lean_unbox(v___x_6706_);
v_res_6714_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v___x_8571__boxed_6713_, v_x_6707_, v___y_6708_, v___y_6709_, v___y_6710_, v___y_6711_);
lean_dec(v___y_6711_);
lean_dec_ref(v___y_6710_);
lean_dec(v___y_6709_);
lean_dec_ref(v___y_6708_);
return v_res_6714_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(lean_object* v_declName_6715_, lean_object* v___y_6716_, lean_object* v___y_6717_, lean_object* v___y_6718_, lean_object* v___y_6719_){
_start:
{
lean_object* v___x_6721_; 
v___x_6721_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionType_spec__0(v_declName_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_);
if (lean_obj_tag(v___x_6721_) == 0)
{
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6777_; 
v_a_6722_ = lean_ctor_get(v___x_6721_, 0);
v_isSharedCheck_6777_ = !lean_is_exclusive(v___x_6721_);
if (v_isSharedCheck_6777_ == 0)
{
v___x_6724_ = v___x_6721_;
v_isShared_6725_ = v_isSharedCheck_6777_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___x_6721_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6777_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
if (lean_obj_tag(v_a_6722_) == 5)
{
lean_object* v_val_6726_; lean_object* v_toConstantVal_6727_; lean_object* v_numParams_6728_; lean_object* v_numIndices_6729_; lean_object* v_ctors_6730_; uint8_t v_isRec_6731_; uint8_t v_isUnsafe_6732_; lean_object* v_type_6733_; uint8_t v___x_6734_; 
v_val_6726_ = lean_ctor_get(v_a_6722_, 0);
lean_inc_ref(v_val_6726_);
lean_dec_ref_known(v_a_6722_, 1);
v_toConstantVal_6727_ = lean_ctor_get(v_val_6726_, 0);
v_numParams_6728_ = lean_ctor_get(v_val_6726_, 1);
lean_inc(v_numParams_6728_);
v_numIndices_6729_ = lean_ctor_get(v_val_6726_, 2);
lean_inc(v_numIndices_6729_);
v_ctors_6730_ = lean_ctor_get(v_val_6726_, 4);
lean_inc(v_ctors_6730_);
v_isRec_6731_ = lean_ctor_get_uint8(v_val_6726_, sizeof(void*)*6);
v_isUnsafe_6732_ = lean_ctor_get_uint8(v_val_6726_, sizeof(void*)*6 + 1);
v_type_6733_ = lean_ctor_get(v_toConstantVal_6727_, 2);
v___x_6734_ = l_Lean_Expr_isProp(v_type_6733_);
if (v___x_6734_ == 0)
{
lean_object* v___x_6735_; lean_object* v___x_6736_; uint8_t v___x_6737_; 
v___x_6735_ = l_Lean_InductiveVal_numTypeFormers(v_val_6726_);
lean_dec_ref(v_val_6726_);
v___x_6736_ = lean_unsigned_to_nat(1u);
v___x_6737_ = lean_nat_dec_eq(v___x_6735_, v___x_6736_);
lean_dec(v___x_6735_);
if (v___x_6737_ == 0)
{
lean_object* v___x_6738_; lean_object* v___x_6740_; 
lean_dec(v_ctors_6730_);
lean_dec(v_numIndices_6729_);
lean_dec(v_numParams_6728_);
v___x_6738_ = lean_box(v___x_6737_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6738_);
v___x_6740_ = v___x_6724_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v___x_6738_);
v___x_6740_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
return v___x_6740_;
}
}
else
{
lean_object* v___x_6742_; uint8_t v___x_6743_; 
v___x_6742_ = lean_unsigned_to_nat(0u);
v___x_6743_ = lean_nat_dec_eq(v_numIndices_6729_, v___x_6742_);
lean_dec(v_numIndices_6729_);
if (v___x_6743_ == 0)
{
lean_object* v___x_6744_; lean_object* v___x_6746_; 
lean_dec(v_ctors_6730_);
lean_dec(v_numParams_6728_);
v___x_6744_ = lean_box(v___x_6743_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6744_);
v___x_6746_ = v___x_6724_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v___x_6744_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
else
{
uint8_t v___x_6748_; 
v___x_6748_ = lean_nat_dec_eq(v_numParams_6728_, v___x_6742_);
lean_dec(v_numParams_6728_);
if (v___x_6748_ == 0)
{
lean_object* v___x_6749_; lean_object* v___x_6751_; 
lean_dec(v_ctors_6730_);
v___x_6749_ = lean_box(v___x_6748_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6749_);
v___x_6751_ = v___x_6724_;
goto v_reusejp_6750_;
}
else
{
lean_object* v_reuseFailAlloc_6752_; 
v_reuseFailAlloc_6752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6752_, 0, v___x_6749_);
v___x_6751_ = v_reuseFailAlloc_6752_;
goto v_reusejp_6750_;
}
v_reusejp_6750_:
{
return v___x_6751_;
}
}
else
{
uint8_t v___x_6753_; 
v___x_6753_ = l_List_isEmpty___redArg(v_ctors_6730_);
if (v___x_6753_ == 0)
{
if (v_isRec_6731_ == 0)
{
if (v_isUnsafe_6732_ == 0)
{
lean_object* v___x_6754_; 
lean_del_object(v___x_6724_);
v___x_6754_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0_spec__0(v_isUnsafe_6732_, v_ctors_6730_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_);
return v___x_6754_;
}
else
{
lean_object* v___x_6755_; lean_object* v___x_6757_; 
lean_dec(v_ctors_6730_);
v___x_6755_ = lean_box(v_isRec_6731_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6755_);
v___x_6757_ = v___x_6724_;
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
}
else
{
lean_object* v___x_6759_; lean_object* v___x_6761_; 
lean_dec(v_ctors_6730_);
v___x_6759_ = lean_box(v___x_6753_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6759_);
v___x_6761_ = v___x_6724_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6762_; 
v_reuseFailAlloc_6762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6762_, 0, v___x_6759_);
v___x_6761_ = v_reuseFailAlloc_6762_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
return v___x_6761_;
}
}
}
else
{
lean_object* v___x_6763_; lean_object* v___x_6765_; 
lean_dec(v_ctors_6730_);
v___x_6763_ = lean_box(v___x_6734_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6763_);
v___x_6765_ = v___x_6724_;
goto v_reusejp_6764_;
}
else
{
lean_object* v_reuseFailAlloc_6766_; 
v_reuseFailAlloc_6766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6766_, 0, v___x_6763_);
v___x_6765_ = v_reuseFailAlloc_6766_;
goto v_reusejp_6764_;
}
v_reusejp_6764_:
{
return v___x_6765_;
}
}
}
}
}
}
else
{
uint8_t v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6770_; 
lean_dec(v_ctors_6730_);
lean_dec(v_numIndices_6729_);
lean_dec(v_numParams_6728_);
lean_dec_ref(v_val_6726_);
v___x_6767_ = 0;
v___x_6768_ = lean_box(v___x_6767_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6768_);
v___x_6770_ = v___x_6724_;
goto v_reusejp_6769_;
}
else
{
lean_object* v_reuseFailAlloc_6771_; 
v_reuseFailAlloc_6771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6771_, 0, v___x_6768_);
v___x_6770_ = v_reuseFailAlloc_6771_;
goto v_reusejp_6769_;
}
v_reusejp_6769_:
{
return v___x_6770_;
}
}
}
else
{
uint8_t v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6775_; 
lean_dec(v_a_6722_);
v___x_6772_ = 0;
v___x_6773_ = lean_box(v___x_6772_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6773_);
v___x_6775_ = v___x_6724_;
goto v_reusejp_6774_;
}
else
{
lean_object* v_reuseFailAlloc_6776_; 
v_reuseFailAlloc_6776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6776_, 0, v___x_6773_);
v___x_6775_ = v_reuseFailAlloc_6776_;
goto v_reusejp_6774_;
}
v_reusejp_6774_:
{
return v___x_6775_;
}
}
}
}
else
{
lean_object* v_a_6778_; lean_object* v___x_6780_; uint8_t v_isShared_6781_; uint8_t v_isSharedCheck_6785_; 
v_a_6778_ = lean_ctor_get(v___x_6721_, 0);
v_isSharedCheck_6785_ = !lean_is_exclusive(v___x_6721_);
if (v_isSharedCheck_6785_ == 0)
{
v___x_6780_ = v___x_6721_;
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
else
{
lean_inc(v_a_6778_);
lean_dec(v___x_6721_);
v___x_6780_ = lean_box(0);
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
v_resetjp_6779_:
{
lean_object* v___x_6783_; 
if (v_isShared_6781_ == 0)
{
v___x_6783_ = v___x_6780_;
goto v_reusejp_6782_;
}
else
{
lean_object* v_reuseFailAlloc_6784_; 
v_reuseFailAlloc_6784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6778_);
v___x_6783_ = v_reuseFailAlloc_6784_;
goto v_reusejp_6782_;
}
v_reusejp_6782_:
{
return v___x_6783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0___boxed(lean_object* v_declName_6786_, lean_object* v___y_6787_, lean_object* v___y_6788_, lean_object* v___y_6789_, lean_object* v___y_6790_, lean_object* v___y_6791_){
_start:
{
lean_object* v_res_6792_; 
v_res_6792_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_6786_, v___y_6787_, v___y_6788_, v___y_6789_, v___y_6790_);
lean_dec(v___y_6790_);
lean_dec_ref(v___y_6789_);
lean_dec(v___y_6788_);
lean_dec_ref(v___y_6787_);
return v_res_6792_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(lean_object* v_e_6793_){
_start:
{
if (lean_obj_tag(v_e_6793_) == 0)
{
uint8_t v___x_6794_; 
v___x_6794_ = 2;
return v___x_6794_;
}
else
{
uint8_t v___x_6795_; 
v___x_6795_ = 0;
return v___x_6795_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5___boxed(lean_object* v_e_6796_){
_start:
{
uint8_t v_res_6797_; lean_object* v_r_6798_; 
v_res_6797_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_e_6796_);
lean_dec_ref(v_e_6796_);
v_r_6798_ = lean_box(v_res_6797_);
return v_r_6798_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(lean_object* v_x_6799_){
_start:
{
if (lean_obj_tag(v_x_6799_) == 0)
{
lean_object* v_a_6801_; lean_object* v___x_6803_; uint8_t v_isShared_6804_; uint8_t v_isSharedCheck_6808_; 
v_a_6801_ = lean_ctor_get(v_x_6799_, 0);
v_isSharedCheck_6808_ = !lean_is_exclusive(v_x_6799_);
if (v_isSharedCheck_6808_ == 0)
{
v___x_6803_ = v_x_6799_;
v_isShared_6804_ = v_isSharedCheck_6808_;
goto v_resetjp_6802_;
}
else
{
lean_inc(v_a_6801_);
lean_dec(v_x_6799_);
v___x_6803_ = lean_box(0);
v_isShared_6804_ = v_isSharedCheck_6808_;
goto v_resetjp_6802_;
}
v_resetjp_6802_:
{
lean_object* v___x_6806_; 
if (v_isShared_6804_ == 0)
{
lean_ctor_set_tag(v___x_6803_, 1);
v___x_6806_ = v___x_6803_;
goto v_reusejp_6805_;
}
else
{
lean_object* v_reuseFailAlloc_6807_; 
v_reuseFailAlloc_6807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6807_, 0, v_a_6801_);
v___x_6806_ = v_reuseFailAlloc_6807_;
goto v_reusejp_6805_;
}
v_reusejp_6805_:
{
return v___x_6806_;
}
}
}
else
{
lean_object* v_a_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
v_a_6809_ = lean_ctor_get(v_x_6799_, 0);
v_isSharedCheck_6816_ = !lean_is_exclusive(v_x_6799_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v_x_6799_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_a_6809_);
lean_dec(v_x_6799_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
lean_ctor_set_tag(v___x_6811_, 0);
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_a_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg___boxed(lean_object* v_x_6817_, lean_object* v___y_6818_){
_start:
{
lean_object* v_res_6819_; 
v_res_6819_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_6817_);
return v_res_6819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(size_t v_sz_6820_, size_t v_i_6821_, lean_object* v_bs_6822_){
_start:
{
uint8_t v___x_6823_; 
v___x_6823_ = lean_usize_dec_lt(v_i_6821_, v_sz_6820_);
if (v___x_6823_ == 0)
{
return v_bs_6822_;
}
else
{
lean_object* v_v_6824_; lean_object* v_msg_6825_; lean_object* v___x_6826_; lean_object* v_bs_x27_6827_; size_t v___x_6828_; size_t v___x_6829_; lean_object* v___x_6830_; 
v_v_6824_ = lean_array_uget_borrowed(v_bs_6822_, v_i_6821_);
v_msg_6825_ = lean_ctor_get(v_v_6824_, 1);
lean_inc_ref(v_msg_6825_);
v___x_6826_ = lean_unsigned_to_nat(0u);
v_bs_x27_6827_ = lean_array_uset(v_bs_6822_, v_i_6821_, v___x_6826_);
v___x_6828_ = ((size_t)1ULL);
v___x_6829_ = lean_usize_add(v_i_6821_, v___x_6828_);
v___x_6830_ = lean_array_uset(v_bs_x27_6827_, v_i_6821_, v_msg_6825_);
v_i_6821_ = v___x_6829_;
v_bs_6822_ = v___x_6830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_6832_, lean_object* v_i_6833_, lean_object* v_bs_6834_){
_start:
{
size_t v_sz_boxed_6835_; size_t v_i_boxed_6836_; lean_object* v_res_6837_; 
v_sz_boxed_6835_ = lean_unbox_usize(v_sz_6832_);
lean_dec(v_sz_6832_);
v_i_boxed_6836_ = lean_unbox_usize(v_i_6833_);
lean_dec(v_i_6833_);
v_res_6837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_boxed_6835_, v_i_boxed_6836_, v_bs_6834_);
return v_res_6837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(lean_object* v_oldTraces_6838_, lean_object* v_data_6839_, lean_object* v_ref_6840_, lean_object* v_msg_6841_, lean_object* v___y_6842_, lean_object* v___y_6843_, lean_object* v___y_6844_, lean_object* v___y_6845_){
_start:
{
lean_object* v_fileName_6847_; lean_object* v_fileMap_6848_; lean_object* v_options_6849_; lean_object* v_currRecDepth_6850_; lean_object* v_maxRecDepth_6851_; lean_object* v_ref_6852_; lean_object* v_currNamespace_6853_; lean_object* v_openDecls_6854_; lean_object* v_initHeartbeats_6855_; lean_object* v_maxHeartbeats_6856_; lean_object* v_quotContext_6857_; lean_object* v_currMacroScope_6858_; uint8_t v_diag_6859_; lean_object* v_cancelTk_x3f_6860_; uint8_t v_suppressElabErrors_6861_; lean_object* v_inheritedTraceOptions_6862_; lean_object* v___x_6863_; lean_object* v_traceState_6864_; lean_object* v_traces_6865_; lean_object* v_ref_6866_; lean_object* v___x_6867_; lean_object* v___x_6868_; size_t v_sz_6869_; size_t v___x_6870_; lean_object* v___x_6871_; lean_object* v_msg_6872_; lean_object* v___x_6873_; lean_object* v_a_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6911_; 
v_fileName_6847_ = lean_ctor_get(v___y_6844_, 0);
v_fileMap_6848_ = lean_ctor_get(v___y_6844_, 1);
v_options_6849_ = lean_ctor_get(v___y_6844_, 2);
v_currRecDepth_6850_ = lean_ctor_get(v___y_6844_, 3);
v_maxRecDepth_6851_ = lean_ctor_get(v___y_6844_, 4);
v_ref_6852_ = lean_ctor_get(v___y_6844_, 5);
v_currNamespace_6853_ = lean_ctor_get(v___y_6844_, 6);
v_openDecls_6854_ = lean_ctor_get(v___y_6844_, 7);
v_initHeartbeats_6855_ = lean_ctor_get(v___y_6844_, 8);
v_maxHeartbeats_6856_ = lean_ctor_get(v___y_6844_, 9);
v_quotContext_6857_ = lean_ctor_get(v___y_6844_, 10);
v_currMacroScope_6858_ = lean_ctor_get(v___y_6844_, 11);
v_diag_6859_ = lean_ctor_get_uint8(v___y_6844_, sizeof(void*)*14);
v_cancelTk_x3f_6860_ = lean_ctor_get(v___y_6844_, 12);
v_suppressElabErrors_6861_ = lean_ctor_get_uint8(v___y_6844_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_6862_ = lean_ctor_get(v___y_6844_, 13);
v___x_6863_ = lean_st_ref_get(v___y_6845_);
v_traceState_6864_ = lean_ctor_get(v___x_6863_, 4);
lean_inc_ref(v_traceState_6864_);
lean_dec(v___x_6863_);
v_traces_6865_ = lean_ctor_get(v_traceState_6864_, 0);
lean_inc_ref(v_traces_6865_);
lean_dec_ref(v_traceState_6864_);
v_ref_6866_ = l_Lean_replaceRef(v_ref_6840_, v_ref_6852_);
lean_inc_ref(v_inheritedTraceOptions_6862_);
lean_inc(v_cancelTk_x3f_6860_);
lean_inc(v_currMacroScope_6858_);
lean_inc(v_quotContext_6857_);
lean_inc(v_maxHeartbeats_6856_);
lean_inc(v_initHeartbeats_6855_);
lean_inc(v_openDecls_6854_);
lean_inc(v_currNamespace_6853_);
lean_inc(v_maxRecDepth_6851_);
lean_inc(v_currRecDepth_6850_);
lean_inc_ref(v_options_6849_);
lean_inc_ref(v_fileMap_6848_);
lean_inc_ref(v_fileName_6847_);
v___x_6867_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_6867_, 0, v_fileName_6847_);
lean_ctor_set(v___x_6867_, 1, v_fileMap_6848_);
lean_ctor_set(v___x_6867_, 2, v_options_6849_);
lean_ctor_set(v___x_6867_, 3, v_currRecDepth_6850_);
lean_ctor_set(v___x_6867_, 4, v_maxRecDepth_6851_);
lean_ctor_set(v___x_6867_, 5, v_ref_6866_);
lean_ctor_set(v___x_6867_, 6, v_currNamespace_6853_);
lean_ctor_set(v___x_6867_, 7, v_openDecls_6854_);
lean_ctor_set(v___x_6867_, 8, v_initHeartbeats_6855_);
lean_ctor_set(v___x_6867_, 9, v_maxHeartbeats_6856_);
lean_ctor_set(v___x_6867_, 10, v_quotContext_6857_);
lean_ctor_set(v___x_6867_, 11, v_currMacroScope_6858_);
lean_ctor_set(v___x_6867_, 12, v_cancelTk_x3f_6860_);
lean_ctor_set(v___x_6867_, 13, v_inheritedTraceOptions_6862_);
lean_ctor_set_uint8(v___x_6867_, sizeof(void*)*14, v_diag_6859_);
lean_ctor_set_uint8(v___x_6867_, sizeof(void*)*14 + 1, v_suppressElabErrors_6861_);
v___x_6868_ = l_Lean_PersistentArray_toArray___redArg(v_traces_6865_);
lean_dec_ref(v_traces_6865_);
v_sz_6869_ = lean_array_size(v___x_6868_);
v___x_6870_ = ((size_t)0ULL);
v___x_6871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3_spec__4(v_sz_6869_, v___x_6870_, v___x_6868_);
v_msg_6872_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_6872_, 0, v_data_6839_);
lean_ctor_set(v_msg_6872_, 1, v_msg_6841_);
lean_ctor_set(v_msg_6872_, 2, v___x_6871_);
v___x_6873_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCtorArg_spec__0_spec__0_spec__4(v_msg_6872_, v___y_6842_, v___y_6843_, v___x_6867_, v___y_6845_);
lean_dec_ref_known(v___x_6867_, 14);
v_a_6874_ = lean_ctor_get(v___x_6873_, 0);
v_isSharedCheck_6911_ = !lean_is_exclusive(v___x_6873_);
if (v_isSharedCheck_6911_ == 0)
{
v___x_6876_ = v___x_6873_;
v_isShared_6877_ = v_isSharedCheck_6911_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_a_6874_);
lean_dec(v___x_6873_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6911_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v___x_6878_; lean_object* v_traceState_6879_; lean_object* v_env_6880_; lean_object* v_nextMacroScope_6881_; lean_object* v_ngen_6882_; lean_object* v_auxDeclNGen_6883_; lean_object* v_cache_6884_; lean_object* v_messages_6885_; lean_object* v_infoState_6886_; lean_object* v_snapshotTasks_6887_; lean_object* v___x_6889_; uint8_t v_isShared_6890_; uint8_t v_isSharedCheck_6910_; 
v___x_6878_ = lean_st_ref_take(v___y_6845_);
v_traceState_6879_ = lean_ctor_get(v___x_6878_, 4);
v_env_6880_ = lean_ctor_get(v___x_6878_, 0);
v_nextMacroScope_6881_ = lean_ctor_get(v___x_6878_, 1);
v_ngen_6882_ = lean_ctor_get(v___x_6878_, 2);
v_auxDeclNGen_6883_ = lean_ctor_get(v___x_6878_, 3);
v_cache_6884_ = lean_ctor_get(v___x_6878_, 5);
v_messages_6885_ = lean_ctor_get(v___x_6878_, 6);
v_infoState_6886_ = lean_ctor_get(v___x_6878_, 7);
v_snapshotTasks_6887_ = lean_ctor_get(v___x_6878_, 8);
v_isSharedCheck_6910_ = !lean_is_exclusive(v___x_6878_);
if (v_isSharedCheck_6910_ == 0)
{
v___x_6889_ = v___x_6878_;
v_isShared_6890_ = v_isSharedCheck_6910_;
goto v_resetjp_6888_;
}
else
{
lean_inc(v_snapshotTasks_6887_);
lean_inc(v_infoState_6886_);
lean_inc(v_messages_6885_);
lean_inc(v_cache_6884_);
lean_inc(v_traceState_6879_);
lean_inc(v_auxDeclNGen_6883_);
lean_inc(v_ngen_6882_);
lean_inc(v_nextMacroScope_6881_);
lean_inc(v_env_6880_);
lean_dec(v___x_6878_);
v___x_6889_ = lean_box(0);
v_isShared_6890_ = v_isSharedCheck_6910_;
goto v_resetjp_6888_;
}
v_resetjp_6888_:
{
uint64_t v_tid_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6908_; 
v_tid_6891_ = lean_ctor_get_uint64(v_traceState_6879_, sizeof(void*)*1);
v_isSharedCheck_6908_ = !lean_is_exclusive(v_traceState_6879_);
if (v_isSharedCheck_6908_ == 0)
{
lean_object* v_unused_6909_; 
v_unused_6909_ = lean_ctor_get(v_traceState_6879_, 0);
lean_dec(v_unused_6909_);
v___x_6893_ = v_traceState_6879_;
v_isShared_6894_ = v_isSharedCheck_6908_;
goto v_resetjp_6892_;
}
else
{
lean_dec(v_traceState_6879_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6908_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6898_; 
v___x_6895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6895_, 0, v_ref_6840_);
lean_ctor_set(v___x_6895_, 1, v_a_6874_);
v___x_6896_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_6838_, v___x_6895_);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 0, v___x_6896_);
v___x_6898_ = v___x_6893_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6907_; 
v_reuseFailAlloc_6907_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6907_, 0, v___x_6896_);
lean_ctor_set_uint64(v_reuseFailAlloc_6907_, sizeof(void*)*1, v_tid_6891_);
v___x_6898_ = v_reuseFailAlloc_6907_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
lean_object* v___x_6900_; 
if (v_isShared_6890_ == 0)
{
lean_ctor_set(v___x_6889_, 4, v___x_6898_);
v___x_6900_ = v___x_6889_;
goto v_reusejp_6899_;
}
else
{
lean_object* v_reuseFailAlloc_6906_; 
v_reuseFailAlloc_6906_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6906_, 0, v_env_6880_);
lean_ctor_set(v_reuseFailAlloc_6906_, 1, v_nextMacroScope_6881_);
lean_ctor_set(v_reuseFailAlloc_6906_, 2, v_ngen_6882_);
lean_ctor_set(v_reuseFailAlloc_6906_, 3, v_auxDeclNGen_6883_);
lean_ctor_set(v_reuseFailAlloc_6906_, 4, v___x_6898_);
lean_ctor_set(v_reuseFailAlloc_6906_, 5, v_cache_6884_);
lean_ctor_set(v_reuseFailAlloc_6906_, 6, v_messages_6885_);
lean_ctor_set(v_reuseFailAlloc_6906_, 7, v_infoState_6886_);
lean_ctor_set(v_reuseFailAlloc_6906_, 8, v_snapshotTasks_6887_);
v___x_6900_ = v_reuseFailAlloc_6906_;
goto v_reusejp_6899_;
}
v_reusejp_6899_:
{
lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6904_; 
v___x_6901_ = lean_st_ref_set(v___y_6845_, v___x_6900_);
v___x_6902_ = lean_box(0);
if (v_isShared_6877_ == 0)
{
lean_ctor_set(v___x_6876_, 0, v___x_6902_);
v___x_6904_ = v___x_6876_;
goto v_reusejp_6903_;
}
else
{
lean_object* v_reuseFailAlloc_6905_; 
v_reuseFailAlloc_6905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6905_, 0, v___x_6902_);
v___x_6904_ = v_reuseFailAlloc_6905_;
goto v_reusejp_6903_;
}
v_reusejp_6903_:
{
return v___x_6904_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3___boxed(lean_object* v_oldTraces_6912_, lean_object* v_data_6913_, lean_object* v_ref_6914_, lean_object* v_msg_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_){
_start:
{
lean_object* v_res_6921_; 
v_res_6921_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6912_, v_data_6913_, v_ref_6914_, v_msg_6915_, v___y_6916_, v___y_6917_, v___y_6918_, v___y_6919_);
lean_dec(v___y_6919_);
lean_dec_ref(v___y_6918_);
lean_dec(v___y_6917_);
lean_dec_ref(v___y_6916_);
return v_res_6921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(lean_object* v_opts_6922_, lean_object* v_opt_6923_){
_start:
{
lean_object* v_name_6924_; lean_object* v_defValue_6925_; lean_object* v_map_6926_; lean_object* v___x_6927_; 
v_name_6924_ = lean_ctor_get(v_opt_6923_, 0);
v_defValue_6925_ = lean_ctor_get(v_opt_6923_, 1);
v_map_6926_ = lean_ctor_get(v_opts_6922_, 0);
v___x_6927_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6926_, v_name_6924_);
if (lean_obj_tag(v___x_6927_) == 0)
{
lean_inc(v_defValue_6925_);
return v_defValue_6925_;
}
else
{
lean_object* v_val_6928_; 
v_val_6928_ = lean_ctor_get(v___x_6927_, 0);
lean_inc(v_val_6928_);
lean_dec_ref_known(v___x_6927_, 1);
if (lean_obj_tag(v_val_6928_) == 3)
{
lean_object* v_v_6929_; 
v_v_6929_ = lean_ctor_get(v_val_6928_, 0);
lean_inc(v_v_6929_);
lean_dec_ref_known(v_val_6928_, 1);
return v_v_6929_;
}
else
{
lean_dec(v_val_6928_);
lean_inc(v_defValue_6925_);
return v_defValue_6925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6___boxed(lean_object* v_opts_6930_, lean_object* v_opt_6931_){
_start:
{
lean_object* v_res_6932_; 
v_res_6932_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6930_, v_opt_6931_);
lean_dec_ref(v_opt_6931_);
lean_dec_ref(v_opts_6930_);
return v_res_6932_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1(void){
_start:
{
lean_object* v___x_6934_; lean_object* v___x_6935_; 
v___x_6934_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__0));
v___x_6935_ = l_Lean_stringToMessageData(v___x_6934_);
return v___x_6935_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2(void){
_start:
{
lean_object* v___x_6936_; double v___x_6937_; 
v___x_6936_ = lean_unsigned_to_nat(1000u);
v___x_6937_ = lean_float_of_nat(v___x_6936_);
return v___x_6937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(lean_object* v_cls_6938_, uint8_t v_collapsed_6939_, lean_object* v_tag_6940_, lean_object* v_opts_6941_, uint8_t v_clsEnabled_6942_, lean_object* v_oldTraces_6943_, lean_object* v_msg_6944_, lean_object* v_resStartStop_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_){
_start:
{
lean_object* v_fst_6951_; lean_object* v_snd_6952_; lean_object* v___y_6954_; lean_object* v___y_6955_; lean_object* v_data_6956_; lean_object* v_fst_6959_; lean_object* v_snd_6960_; lean_object* v___x_6961_; uint8_t v___x_6962_; lean_object* v___y_6964_; lean_object* v_a_6965_; uint8_t v___y_6980_; double v___y_7011_; 
v_fst_6951_ = lean_ctor_get(v_resStartStop_6945_, 0);
lean_inc(v_fst_6951_);
v_snd_6952_ = lean_ctor_get(v_resStartStop_6945_, 1);
lean_inc(v_snd_6952_);
lean_dec_ref(v_resStartStop_6945_);
v_fst_6959_ = lean_ctor_get(v_snd_6952_, 0);
lean_inc(v_fst_6959_);
v_snd_6960_ = lean_ctor_get(v_snd_6952_, 1);
lean_inc(v_snd_6960_);
lean_dec(v_snd_6952_);
v___x_6961_ = l_Lean_trace_profiler;
v___x_6962_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6941_, v___x_6961_);
if (v___x_6962_ == 0)
{
v___y_6980_ = v___x_6962_;
goto v___jp_6979_;
}
else
{
lean_object* v___x_7016_; uint8_t v___x_7017_; 
v___x_7016_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7017_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_opts_6941_, v___x_7016_);
if (v___x_7017_ == 0)
{
lean_object* v___x_7018_; lean_object* v___x_7019_; double v___x_7020_; double v___x_7021_; double v___x_7022_; 
v___x_7018_ = l_Lean_trace_profiler_threshold;
v___x_7019_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6941_, v___x_7018_);
v___x_7020_ = lean_float_of_nat(v___x_7019_);
v___x_7021_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__2);
v___x_7022_ = lean_float_div(v___x_7020_, v___x_7021_);
v___y_7011_ = v___x_7022_;
goto v___jp_7010_;
}
else
{
lean_object* v___x_7023_; lean_object* v___x_7024_; double v___x_7025_; 
v___x_7023_ = l_Lean_trace_profiler_threshold;
v___x_7024_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__6(v_opts_6941_, v___x_7023_);
v___x_7025_ = lean_float_of_nat(v___x_7024_);
v___y_7011_ = v___x_7025_;
goto v___jp_7010_;
}
}
v___jp_6953_:
{
lean_object* v___x_6957_; 
lean_inc(v___y_6955_);
v___x_6957_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__3(v_oldTraces_6943_, v_data_6956_, v___y_6955_, v___y_6954_, v___y_6946_, v___y_6947_, v___y_6948_, v___y_6949_);
if (lean_obj_tag(v___x_6957_) == 0)
{
lean_object* v___x_6958_; 
lean_dec_ref_known(v___x_6957_, 1);
v___x_6958_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_6951_);
return v___x_6958_;
}
else
{
lean_dec(v_fst_6951_);
return v___x_6957_;
}
}
v___jp_6963_:
{
uint8_t v_result_6966_; lean_object* v___x_6967_; lean_object* v___x_6968_; double v___x_6969_; lean_object* v_data_6970_; 
v_result_6966_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__5(v_fst_6951_);
v___x_6967_ = lean_box(v_result_6966_);
v___x_6968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6968_, 0, v___x_6967_);
v___x_6969_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__0);
lean_inc_ref(v_tag_6940_);
lean_inc_ref(v___x_6968_);
lean_inc(v_cls_6938_);
v_data_6970_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6970_, 0, v_cls_6938_);
lean_ctor_set(v_data_6970_, 1, v___x_6968_);
lean_ctor_set(v_data_6970_, 2, v_tag_6940_);
lean_ctor_set_float(v_data_6970_, sizeof(void*)*3, v___x_6969_);
lean_ctor_set_float(v_data_6970_, sizeof(void*)*3 + 8, v___x_6969_);
lean_ctor_set_uint8(v_data_6970_, sizeof(void*)*3 + 16, v_collapsed_6939_);
if (v___x_6962_ == 0)
{
lean_dec_ref_known(v___x_6968_, 1);
lean_dec(v_snd_6960_);
lean_dec(v_fst_6959_);
lean_dec_ref(v_tag_6940_);
lean_dec(v_cls_6938_);
v___y_6954_ = v_a_6965_;
v___y_6955_ = v___y_6964_;
v_data_6956_ = v_data_6970_;
goto v___jp_6953_;
}
else
{
lean_object* v_data_6971_; double v___x_6972_; double v___x_6973_; 
lean_dec_ref_known(v_data_6970_, 3);
v_data_6971_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6971_, 0, v_cls_6938_);
lean_ctor_set(v_data_6971_, 1, v___x_6968_);
lean_ctor_set(v_data_6971_, 2, v_tag_6940_);
v___x_6972_ = lean_unbox_float(v_fst_6959_);
lean_dec(v_fst_6959_);
lean_ctor_set_float(v_data_6971_, sizeof(void*)*3, v___x_6972_);
v___x_6973_ = lean_unbox_float(v_snd_6960_);
lean_dec(v_snd_6960_);
lean_ctor_set_float(v_data_6971_, sizeof(void*)*3 + 8, v___x_6973_);
lean_ctor_set_uint8(v_data_6971_, sizeof(void*)*3 + 16, v_collapsed_6939_);
v___y_6954_ = v_a_6965_;
v___y_6955_ = v___y_6964_;
v_data_6956_ = v_data_6971_;
goto v___jp_6953_;
}
}
v___jp_6974_:
{
lean_object* v_ref_6975_; lean_object* v___x_6976_; 
v_ref_6975_ = lean_ctor_get(v___y_6948_, 5);
lean_inc(v___y_6949_);
lean_inc_ref(v___y_6948_);
lean_inc(v___y_6947_);
lean_inc_ref(v___y_6946_);
lean_inc(v_fst_6951_);
v___x_6976_ = lean_apply_6(v_msg_6944_, v_fst_6951_, v___y_6946_, v___y_6947_, v___y_6948_, v___y_6949_, lean_box(0));
if (lean_obj_tag(v___x_6976_) == 0)
{
lean_object* v_a_6977_; 
v_a_6977_ = lean_ctor_get(v___x_6976_, 0);
lean_inc(v_a_6977_);
lean_dec_ref_known(v___x_6976_, 1);
v___y_6964_ = v_ref_6975_;
v_a_6965_ = v_a_6977_;
goto v___jp_6963_;
}
else
{
lean_object* v___x_6978_; 
lean_dec_ref_known(v___x_6976_, 1);
v___x_6978_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___closed__1);
v___y_6964_ = v_ref_6975_;
v_a_6965_ = v___x_6978_;
goto v___jp_6963_;
}
}
v___jp_6979_:
{
if (v_clsEnabled_6942_ == 0)
{
if (v___y_6980_ == 0)
{
lean_object* v___x_6981_; lean_object* v_traceState_6982_; lean_object* v_env_6983_; lean_object* v_nextMacroScope_6984_; lean_object* v_ngen_6985_; lean_object* v_auxDeclNGen_6986_; lean_object* v_cache_6987_; lean_object* v_messages_6988_; lean_object* v_infoState_6989_; lean_object* v_snapshotTasks_6990_; lean_object* v___x_6992_; uint8_t v_isShared_6993_; uint8_t v_isSharedCheck_7009_; 
lean_dec(v_snd_6960_);
lean_dec(v_fst_6959_);
lean_dec_ref(v_msg_6944_);
lean_dec_ref(v_tag_6940_);
lean_dec(v_cls_6938_);
v___x_6981_ = lean_st_ref_take(v___y_6949_);
v_traceState_6982_ = lean_ctor_get(v___x_6981_, 4);
v_env_6983_ = lean_ctor_get(v___x_6981_, 0);
v_nextMacroScope_6984_ = lean_ctor_get(v___x_6981_, 1);
v_ngen_6985_ = lean_ctor_get(v___x_6981_, 2);
v_auxDeclNGen_6986_ = lean_ctor_get(v___x_6981_, 3);
v_cache_6987_ = lean_ctor_get(v___x_6981_, 5);
v_messages_6988_ = lean_ctor_get(v___x_6981_, 6);
v_infoState_6989_ = lean_ctor_get(v___x_6981_, 7);
v_snapshotTasks_6990_ = lean_ctor_get(v___x_6981_, 8);
v_isSharedCheck_7009_ = !lean_is_exclusive(v___x_6981_);
if (v_isSharedCheck_7009_ == 0)
{
v___x_6992_ = v___x_6981_;
v_isShared_6993_ = v_isSharedCheck_7009_;
goto v_resetjp_6991_;
}
else
{
lean_inc(v_snapshotTasks_6990_);
lean_inc(v_infoState_6989_);
lean_inc(v_messages_6988_);
lean_inc(v_cache_6987_);
lean_inc(v_traceState_6982_);
lean_inc(v_auxDeclNGen_6986_);
lean_inc(v_ngen_6985_);
lean_inc(v_nextMacroScope_6984_);
lean_inc(v_env_6983_);
lean_dec(v___x_6981_);
v___x_6992_ = lean_box(0);
v_isShared_6993_ = v_isSharedCheck_7009_;
goto v_resetjp_6991_;
}
v_resetjp_6991_:
{
uint64_t v_tid_6994_; lean_object* v_traces_6995_; lean_object* v___x_6997_; uint8_t v_isShared_6998_; uint8_t v_isSharedCheck_7008_; 
v_tid_6994_ = lean_ctor_get_uint64(v_traceState_6982_, sizeof(void*)*1);
v_traces_6995_ = lean_ctor_get(v_traceState_6982_, 0);
v_isSharedCheck_7008_ = !lean_is_exclusive(v_traceState_6982_);
if (v_isSharedCheck_7008_ == 0)
{
v___x_6997_ = v_traceState_6982_;
v_isShared_6998_ = v_isSharedCheck_7008_;
goto v_resetjp_6996_;
}
else
{
lean_inc(v_traces_6995_);
lean_dec(v_traceState_6982_);
v___x_6997_ = lean_box(0);
v_isShared_6998_ = v_isSharedCheck_7008_;
goto v_resetjp_6996_;
}
v_resetjp_6996_:
{
lean_object* v___x_6999_; lean_object* v___x_7001_; 
v___x_6999_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6943_, v_traces_6995_);
lean_dec_ref(v_traces_6995_);
if (v_isShared_6998_ == 0)
{
lean_ctor_set(v___x_6997_, 0, v___x_6999_);
v___x_7001_ = v___x_6997_;
goto v_reusejp_7000_;
}
else
{
lean_object* v_reuseFailAlloc_7007_; 
v_reuseFailAlloc_7007_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_7007_, 0, v___x_6999_);
lean_ctor_set_uint64(v_reuseFailAlloc_7007_, sizeof(void*)*1, v_tid_6994_);
v___x_7001_ = v_reuseFailAlloc_7007_;
goto v_reusejp_7000_;
}
v_reusejp_7000_:
{
lean_object* v___x_7003_; 
if (v_isShared_6993_ == 0)
{
lean_ctor_set(v___x_6992_, 4, v___x_7001_);
v___x_7003_ = v___x_6992_;
goto v_reusejp_7002_;
}
else
{
lean_object* v_reuseFailAlloc_7006_; 
v_reuseFailAlloc_7006_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_env_6983_);
lean_ctor_set(v_reuseFailAlloc_7006_, 1, v_nextMacroScope_6984_);
lean_ctor_set(v_reuseFailAlloc_7006_, 2, v_ngen_6985_);
lean_ctor_set(v_reuseFailAlloc_7006_, 3, v_auxDeclNGen_6986_);
lean_ctor_set(v_reuseFailAlloc_7006_, 4, v___x_7001_);
lean_ctor_set(v_reuseFailAlloc_7006_, 5, v_cache_6987_);
lean_ctor_set(v_reuseFailAlloc_7006_, 6, v_messages_6988_);
lean_ctor_set(v_reuseFailAlloc_7006_, 7, v_infoState_6989_);
lean_ctor_set(v_reuseFailAlloc_7006_, 8, v_snapshotTasks_6990_);
v___x_7003_ = v_reuseFailAlloc_7006_;
goto v_reusejp_7002_;
}
v_reusejp_7002_:
{
lean_object* v___x_7004_; lean_object* v___x_7005_; 
v___x_7004_ = lean_st_ref_set(v___y_6949_, v___x_7003_);
v___x_7005_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_fst_6951_);
return v___x_7005_;
}
}
}
}
}
else
{
goto v___jp_6974_;
}
}
else
{
goto v___jp_6974_;
}
}
v___jp_7010_:
{
double v___x_7012_; double v___x_7013_; double v___x_7014_; uint8_t v___x_7015_; 
v___x_7012_ = lean_unbox_float(v_snd_6960_);
v___x_7013_ = lean_unbox_float(v_fst_6959_);
v___x_7014_ = lean_float_sub(v___x_7012_, v___x_7013_);
v___x_7015_ = lean_float_decLt(v___y_7011_, v___x_7014_);
v___y_6980_ = v___x_7015_;
goto v___jp_6979_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2___boxed(lean_object* v_cls_7026_, lean_object* v_collapsed_7027_, lean_object* v_tag_7028_, lean_object* v_opts_7029_, lean_object* v_clsEnabled_7030_, lean_object* v_oldTraces_7031_, lean_object* v_msg_7032_, lean_object* v_resStartStop_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_){
_start:
{
uint8_t v_collapsed_boxed_7039_; uint8_t v_clsEnabled_boxed_7040_; lean_object* v_res_7041_; 
v_collapsed_boxed_7039_ = lean_unbox(v_collapsed_7027_);
v_clsEnabled_boxed_7040_ = lean_unbox(v_clsEnabled_7030_);
v_res_7041_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v_cls_7026_, v_collapsed_boxed_7039_, v_tag_7028_, v_opts_7029_, v_clsEnabled_boxed_7040_, v_oldTraces_7031_, v_msg_7032_, v_resStartStop_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_);
lean_dec(v___y_7037_);
lean_dec_ref(v___y_7036_);
lean_dec(v___y_7035_);
lean_dec_ref(v___y_7034_);
lean_dec_ref(v_opts_7029_);
return v_res_7041_;
}
}
static double _init_l_Lean_mkNoConfusion___closed__0(void){
_start:
{
lean_object* v___x_7042_; double v___x_7043_; 
v___x_7042_ = lean_unsigned_to_nat(1000000000u);
v___x_7043_ = lean_float_of_nat(v___x_7042_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion(lean_object* v_declName_7044_, lean_object* v_a_7045_, lean_object* v_a_7046_, lean_object* v_a_7047_, lean_object* v_a_7048_){
_start:
{
lean_object* v_options_7050_; uint8_t v_hasTrace_7051_; 
v_options_7050_ = lean_ctor_get(v_a_7047_, 2);
v_hasTrace_7051_ = lean_ctor_get_uint8(v_options_7050_, sizeof(void*)*1);
if (v_hasTrace_7051_ == 0)
{
lean_object* v___x_7052_; 
lean_inc(v_declName_7044_);
v___x_7052_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
if (lean_obj_tag(v___x_7052_) == 0)
{
lean_object* v_a_7053_; uint8_t v___x_7054_; 
v_a_7053_ = lean_ctor_get(v___x_7052_, 0);
lean_inc(v_a_7053_);
lean_dec_ref_known(v___x_7052_, 1);
v___x_7054_ = lean_unbox(v_a_7053_);
lean_dec(v_a_7053_);
if (v___x_7054_ == 0)
{
lean_object* v___x_7055_; 
v___x_7055_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7055_;
}
else
{
lean_object* v___x_7056_; 
v___x_7056_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7056_;
}
}
else
{
lean_object* v_a_7057_; lean_object* v___x_7059_; uint8_t v_isShared_7060_; uint8_t v_isSharedCheck_7064_; 
lean_dec(v_declName_7044_);
v_a_7057_ = lean_ctor_get(v___x_7052_, 0);
v_isSharedCheck_7064_ = !lean_is_exclusive(v___x_7052_);
if (v_isSharedCheck_7064_ == 0)
{
v___x_7059_ = v___x_7052_;
v_isShared_7060_ = v_isSharedCheck_7064_;
goto v_resetjp_7058_;
}
else
{
lean_inc(v_a_7057_);
lean_dec(v___x_7052_);
v___x_7059_ = lean_box(0);
v_isShared_7060_ = v_isSharedCheck_7064_;
goto v_resetjp_7058_;
}
v_resetjp_7058_:
{
lean_object* v___x_7062_; 
if (v_isShared_7060_ == 0)
{
v___x_7062_ = v___x_7059_;
goto v_reusejp_7061_;
}
else
{
lean_object* v_reuseFailAlloc_7063_; 
v_reuseFailAlloc_7063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7063_, 0, v_a_7057_);
v___x_7062_ = v_reuseFailAlloc_7063_;
goto v_reusejp_7061_;
}
v_reusejp_7061_:
{
return v___x_7062_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_7065_; lean_object* v___f_7066_; lean_object* v___x_7067_; lean_object* v___x_7068_; lean_object* v___x_7069_; uint8_t v___x_7070_; lean_object* v___y_7072_; lean_object* v___y_7073_; lean_object* v_a_7074_; lean_object* v___y_7087_; lean_object* v___y_7088_; lean_object* v_a_7089_; lean_object* v___y_7092_; lean_object* v___y_7093_; lean_object* v___y_7094_; lean_object* v___y_7105_; lean_object* v___y_7106_; lean_object* v_a_7107_; lean_object* v___y_7117_; lean_object* v___y_7118_; lean_object* v_a_7119_; lean_object* v___y_7122_; lean_object* v___y_7123_; lean_object* v___y_7124_; 
v_inheritedTraceOptions_7065_ = lean_ctor_get(v_a_7047_, 13);
lean_inc(v_declName_7044_);
v___f_7066_ = lean_alloc_closure((void*)(l_Lean_mkNoConfusion___lam__0___boxed), 7, 1);
lean_closure_set(v___f_7066_, 0, v_declName_7044_);
v___x_7067_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7068_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__0___closed__1));
v___x_7069_ = lean_obj_once(&l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2, &l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2_once, _init_l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCoreImp___closed__2);
v___x_7070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_7065_, v_options_7050_, v___x_7069_);
if (v___x_7070_ == 0)
{
lean_object* v___x_7153_; uint8_t v___x_7154_; 
v___x_7153_ = l_Lean_trace_profiler;
v___x_7154_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7050_, v___x_7153_);
if (v___x_7154_ == 0)
{
lean_object* v___x_7155_; 
lean_dec_ref(v___f_7066_);
lean_inc(v_declName_7044_);
v___x_7155_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
if (lean_obj_tag(v___x_7155_) == 0)
{
lean_object* v_a_7156_; uint8_t v___x_7157_; 
v_a_7156_ = lean_ctor_get(v___x_7155_, 0);
lean_inc(v_a_7156_);
lean_dec_ref_known(v___x_7155_, 1);
v___x_7157_ = lean_unbox(v_a_7156_);
lean_dec(v_a_7156_);
if (v___x_7157_ == 0)
{
lean_object* v___x_7158_; 
v___x_7158_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7158_;
}
else
{
lean_object* v___x_7159_; 
v___x_7159_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7159_;
}
}
else
{
lean_object* v_a_7160_; lean_object* v___x_7162_; uint8_t v_isShared_7163_; uint8_t v_isSharedCheck_7167_; 
lean_dec(v_declName_7044_);
v_a_7160_ = lean_ctor_get(v___x_7155_, 0);
v_isSharedCheck_7167_ = !lean_is_exclusive(v___x_7155_);
if (v_isSharedCheck_7167_ == 0)
{
v___x_7162_ = v___x_7155_;
v_isShared_7163_ = v_isSharedCheck_7167_;
goto v_resetjp_7161_;
}
else
{
lean_inc(v_a_7160_);
lean_dec(v___x_7155_);
v___x_7162_ = lean_box(0);
v_isShared_7163_ = v_isSharedCheck_7167_;
goto v_resetjp_7161_;
}
v_resetjp_7161_:
{
lean_object* v___x_7165_; 
if (v_isShared_7163_ == 0)
{
v___x_7165_ = v___x_7162_;
goto v_reusejp_7164_;
}
else
{
lean_object* v_reuseFailAlloc_7166_; 
v_reuseFailAlloc_7166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7166_, 0, v_a_7160_);
v___x_7165_ = v_reuseFailAlloc_7166_;
goto v_reusejp_7164_;
}
v_reusejp_7164_:
{
return v___x_7165_;
}
}
}
}
else
{
goto v___jp_7134_;
}
}
else
{
goto v___jp_7134_;
}
v___jp_7071_:
{
lean_object* v___x_7075_; double v___x_7076_; double v___x_7077_; double v___x_7078_; double v___x_7079_; double v___x_7080_; lean_object* v___x_7081_; lean_object* v___x_7082_; lean_object* v___x_7083_; lean_object* v___x_7084_; lean_object* v___x_7085_; 
v___x_7075_ = lean_io_mono_nanos_now();
v___x_7076_ = lean_float_of_nat(v___y_7072_);
v___x_7077_ = lean_float_once(&l_Lean_mkNoConfusion___closed__0, &l_Lean_mkNoConfusion___closed__0_once, _init_l_Lean_mkNoConfusion___closed__0);
v___x_7078_ = lean_float_div(v___x_7076_, v___x_7077_);
v___x_7079_ = lean_float_of_nat(v___x_7075_);
v___x_7080_ = lean_float_div(v___x_7079_, v___x_7077_);
v___x_7081_ = lean_box_float(v___x_7078_);
v___x_7082_ = lean_box_float(v___x_7080_);
v___x_7083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7083_, 0, v___x_7081_);
lean_ctor_set(v___x_7083_, 1, v___x_7082_);
v___x_7084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7084_, 0, v_a_7074_);
lean_ctor_set(v___x_7084_, 1, v___x_7083_);
v___x_7085_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7067_, v_hasTrace_7051_, v___x_7068_, v_options_7050_, v___x_7070_, v___y_7073_, v___f_7066_, v___x_7084_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7085_;
}
v___jp_7086_:
{
lean_object* v___x_7090_; 
v___x_7090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7090_, 0, v_a_7089_);
v___y_7072_ = v___y_7087_;
v___y_7073_ = v___y_7088_;
v_a_7074_ = v___x_7090_;
goto v___jp_7071_;
}
v___jp_7091_:
{
if (lean_obj_tag(v___y_7094_) == 0)
{
lean_object* v_a_7095_; lean_object* v___x_7097_; uint8_t v_isShared_7098_; uint8_t v_isSharedCheck_7102_; 
v_a_7095_ = lean_ctor_get(v___y_7094_, 0);
v_isSharedCheck_7102_ = !lean_is_exclusive(v___y_7094_);
if (v_isSharedCheck_7102_ == 0)
{
v___x_7097_ = v___y_7094_;
v_isShared_7098_ = v_isSharedCheck_7102_;
goto v_resetjp_7096_;
}
else
{
lean_inc(v_a_7095_);
lean_dec(v___y_7094_);
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
v___y_7072_ = v___y_7092_;
v___y_7073_ = v___y_7093_;
v_a_7074_ = v___x_7100_;
goto v___jp_7071_;
}
}
}
else
{
lean_object* v_a_7103_; 
v_a_7103_ = lean_ctor_get(v___y_7094_, 0);
lean_inc(v_a_7103_);
lean_dec_ref_known(v___y_7094_, 1);
v___y_7087_ = v___y_7092_;
v___y_7088_ = v___y_7093_;
v_a_7089_ = v_a_7103_;
goto v___jp_7086_;
}
}
v___jp_7104_:
{
lean_object* v___x_7108_; double v___x_7109_; double v___x_7110_; lean_object* v___x_7111_; lean_object* v___x_7112_; lean_object* v___x_7113_; lean_object* v___x_7114_; lean_object* v___x_7115_; 
v___x_7108_ = lean_io_get_num_heartbeats();
v___x_7109_ = lean_float_of_nat(v___y_7105_);
v___x_7110_ = lean_float_of_nat(v___x_7108_);
v___x_7111_ = lean_box_float(v___x_7109_);
v___x_7112_ = lean_box_float(v___x_7110_);
v___x_7113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7113_, 0, v___x_7111_);
lean_ctor_set(v___x_7113_, 1, v___x_7112_);
v___x_7114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7114_, 0, v_a_7107_);
lean_ctor_set(v___x_7114_, 1, v___x_7113_);
v___x_7115_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2(v___x_7067_, v_hasTrace_7051_, v___x_7068_, v_options_7050_, v___x_7070_, v___y_7106_, v___f_7066_, v___x_7114_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
return v___x_7115_;
}
v___jp_7116_:
{
lean_object* v___x_7120_; 
v___x_7120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7120_, 0, v_a_7119_);
v___y_7105_ = v___y_7117_;
v___y_7106_ = v___y_7118_;
v_a_7107_ = v___x_7120_;
goto v___jp_7104_;
}
v___jp_7121_:
{
if (lean_obj_tag(v___y_7124_) == 0)
{
lean_object* v_a_7125_; lean_object* v___x_7127_; uint8_t v_isShared_7128_; uint8_t v_isSharedCheck_7132_; 
v_a_7125_ = lean_ctor_get(v___y_7124_, 0);
v_isSharedCheck_7132_ = !lean_is_exclusive(v___y_7124_);
if (v_isSharedCheck_7132_ == 0)
{
v___x_7127_ = v___y_7124_;
v_isShared_7128_ = v_isSharedCheck_7132_;
goto v_resetjp_7126_;
}
else
{
lean_inc(v_a_7125_);
lean_dec(v___y_7124_);
v___x_7127_ = lean_box(0);
v_isShared_7128_ = v_isSharedCheck_7132_;
goto v_resetjp_7126_;
}
v_resetjp_7126_:
{
lean_object* v___x_7130_; 
if (v_isShared_7128_ == 0)
{
lean_ctor_set_tag(v___x_7127_, 1);
v___x_7130_ = v___x_7127_;
goto v_reusejp_7129_;
}
else
{
lean_object* v_reuseFailAlloc_7131_; 
v_reuseFailAlloc_7131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7131_, 0, v_a_7125_);
v___x_7130_ = v_reuseFailAlloc_7131_;
goto v_reusejp_7129_;
}
v_reusejp_7129_:
{
v___y_7105_ = v___y_7122_;
v___y_7106_ = v___y_7123_;
v_a_7107_ = v___x_7130_;
goto v___jp_7104_;
}
}
}
else
{
lean_object* v_a_7133_; 
v_a_7133_ = lean_ctor_get(v___y_7124_, 0);
lean_inc(v_a_7133_);
lean_dec_ref_known(v___y_7124_, 1);
v___y_7117_ = v___y_7122_;
v___y_7118_ = v___y_7123_;
v_a_7119_ = v_a_7133_;
goto v___jp_7116_;
}
}
v___jp_7134_:
{
lean_object* v___x_7135_; lean_object* v_a_7136_; lean_object* v___x_7137_; uint8_t v___x_7138_; 
v___x_7135_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkNoConfusion_spec__1___redArg(v_a_7048_);
v_a_7136_ = lean_ctor_get(v___x_7135_, 0);
lean_inc(v_a_7136_);
lean_dec_ref(v___x_7135_);
v___x_7137_ = l_Lean_trace_profiler_useHeartbeats;
v___x_7138_ = l_Lean_Option_get___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_canUseLinear_spec__0(v_options_7050_, v___x_7137_);
if (v___x_7138_ == 0)
{
lean_object* v___x_7139_; lean_object* v___x_7140_; 
v___x_7139_ = lean_io_mono_nanos_now();
lean_inc(v_declName_7044_);
v___x_7140_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
if (lean_obj_tag(v___x_7140_) == 0)
{
lean_object* v_a_7141_; uint8_t v___x_7142_; 
v_a_7141_ = lean_ctor_get(v___x_7140_, 0);
lean_inc(v_a_7141_);
lean_dec_ref_known(v___x_7140_, 1);
v___x_7142_ = lean_unbox(v_a_7141_);
lean_dec(v_a_7141_);
if (v___x_7142_ == 0)
{
lean_object* v___x_7143_; 
v___x_7143_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
v___y_7092_ = v___x_7139_;
v___y_7093_ = v_a_7136_;
v___y_7094_ = v___x_7143_;
goto v___jp_7091_;
}
else
{
lean_object* v___x_7144_; 
v___x_7144_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
v___y_7092_ = v___x_7139_;
v___y_7093_ = v_a_7136_;
v___y_7094_ = v___x_7144_;
goto v___jp_7091_;
}
}
else
{
lean_object* v_a_7145_; 
lean_dec(v_declName_7044_);
v_a_7145_ = lean_ctor_get(v___x_7140_, 0);
lean_inc(v_a_7145_);
lean_dec_ref_known(v___x_7140_, 1);
v___y_7087_ = v___x_7139_;
v___y_7088_ = v_a_7136_;
v_a_7089_ = v_a_7145_;
goto v___jp_7086_;
}
}
else
{
lean_object* v___x_7146_; lean_object* v___x_7147_; 
v___x_7146_ = lean_io_get_num_heartbeats();
lean_inc(v_declName_7044_);
v___x_7147_ = l_Lean_isEnumType___at___00Lean_mkNoConfusion_spec__0(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
if (lean_obj_tag(v___x_7147_) == 0)
{
lean_object* v_a_7148_; uint8_t v___x_7149_; 
v_a_7148_ = lean_ctor_get(v___x_7147_, 0);
lean_inc(v_a_7148_);
lean_dec_ref_known(v___x_7147_, 1);
v___x_7149_ = lean_unbox(v_a_7148_);
lean_dec(v_a_7148_);
if (v___x_7149_ == 0)
{
lean_object* v___x_7150_; 
v___x_7150_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionCore(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
v___y_7122_ = v___x_7146_;
v___y_7123_ = v_a_7136_;
v___y_7124_ = v___x_7150_;
goto v___jp_7121_;
}
else
{
lean_object* v___x_7151_; 
v___x_7151_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkNoConfusionEnum(v_declName_7044_, v_a_7045_, v_a_7046_, v_a_7047_, v_a_7048_);
v___y_7122_ = v___x_7146_;
v___y_7123_ = v_a_7136_;
v___y_7124_ = v___x_7151_;
goto v___jp_7121_;
}
}
else
{
lean_object* v_a_7152_; 
lean_dec(v_declName_7044_);
v_a_7152_ = lean_ctor_get(v___x_7147_, 0);
lean_inc(v_a_7152_);
lean_dec_ref_known(v___x_7147_, 1);
v___y_7117_ = v___x_7146_;
v___y_7118_ = v_a_7136_;
v_a_7119_ = v_a_7152_;
goto v___jp_7116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkNoConfusion___boxed(lean_object* v_declName_7168_, lean_object* v_a_7169_, lean_object* v_a_7170_, lean_object* v_a_7171_, lean_object* v_a_7172_, lean_object* v_a_7173_){
_start:
{
lean_object* v_res_7174_; 
v_res_7174_ = l_Lean_mkNoConfusion(v_declName_7168_, v_a_7169_, v_a_7170_, v_a_7171_, v_a_7172_);
lean_dec(v_a_7172_);
lean_dec_ref(v_a_7171_);
lean_dec(v_a_7170_);
lean_dec_ref(v_a_7169_);
return v_res_7174_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(lean_object* v_00_u03b1_7175_, lean_object* v_x_7176_, lean_object* v___y_7177_, lean_object* v___y_7178_, lean_object* v___y_7179_, lean_object* v___y_7180_){
_start:
{
lean_object* v___x_7182_; 
v___x_7182_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___redArg(v_x_7176_);
return v___x_7182_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4___boxed(lean_object* v_00_u03b1_7183_, lean_object* v_x_7184_, lean_object* v___y_7185_, lean_object* v___y_7186_, lean_object* v___y_7187_, lean_object* v___y_7188_, lean_object* v___y_7189_){
_start:
{
lean_object* v_res_7190_; 
v_res_7190_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkNoConfusion_spec__2_spec__4(v_00_u03b1_7183_, v_x_7184_, v___y_7185_, v___y_7186_, v___y_7187_, v___y_7188_);
lean_dec(v___y_7188_);
lean_dec_ref(v___y_7187_);
lean_dec(v___y_7186_);
lean_dec_ref(v___y_7185_);
return v_res_7190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7226_; uint8_t v___x_7227_; lean_object* v___x_7228_; lean_object* v___x_7229_; 
v___x_7226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_NoConfusion_0__Lean_mkEqNDRecTelescope_spec__3___closed__1));
v___x_7227_ = 0;
v___x_7228_ = ((lean_object*)(l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_));
v___x_7229_ = l_Lean_registerTraceClass(v___x_7226_, v___x_7227_, v___x_7228_);
return v___x_7229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2____boxed(lean_object* v_a_7230_){
_start:
{
lean_object* v_res_7231_; 
v_res_7231_ = l___private_Lean_Meta_Constructions_NoConfusion_0__Lean_initFn_00___x40_Lean_Meta_Constructions_NoConfusion_1240126624____hygCtx___hyg_2_();
return v_res_7231_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_NoConfusion(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
