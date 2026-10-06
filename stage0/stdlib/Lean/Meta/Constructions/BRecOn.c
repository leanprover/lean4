// Lean compiler output
// Module: Lean.Meta.Constructions.BRecOn
// Imports: public import Lean.Meta.Basic import Lean.Meta.PProdN import Lean.Meta.Tactic.Cases import Lean.Meta.Tactic.Refl
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPProdMk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_mkBelowName(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkBRecOnName(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_ofFn___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPProdFstM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPProdSndM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Constructions.BRecOn"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.Constructions.BRecOn.0.Lean.mkBelowFromRec"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "assertion violation: refArgs.size > nParams + recVal.numMotives + recVal.numMinors\n    "};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "type of type of major premise "};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " not a type former"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "recursor "};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " has no levelParams"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " not a .recInfo"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkBelow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_mkBelow___closed__0 = (const lean_object*)&l_Lean_mkBelow___closed__0_value;
static const lean_string_object l_Lean_mkBelow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkBelow"};
static const lean_object* l_Lean_mkBelow___closed__1 = (const lean_object*)&l_Lean_mkBelow___closed__1_value;
static const lean_ctor_object l_Lean_mkBelow___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkBelow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkBelow___closed__2_value_aux_0),((lean_object*)&l_Lean_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(219, 145, 247, 215, 113, 151, 53, 217)}};
static const lean_object* l_Lean_mkBelow___closed__2 = (const lean_object*)&l_Lean_mkBelow___closed__2_value;
static const lean_string_object l_Lean_mkBelow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkBelow___closed__3 = (const lean_object*)&l_Lean_mkBelow___closed__3_value;
static const lean_string_object l_Lean_mkBelow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_mkBelow___closed__4 = (const lean_object*)&l_Lean_mkBelow___closed__4_value;
static const lean_ctor_object l_Lean_mkBelow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_mkBelow___closed__5 = (const lean_object*)&l_Lean_mkBelow___closed__5_value;
static lean_once_cell_t l_Lean_mkBelow___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkBelow___closed__6;
static lean_once_cell_t l_Lean_mkBelow___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkBelow___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Did not find "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "F_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "_private.Lean.Meta.Constructions.BRecOn.0.Lean.mkBRecOnFromRec"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1;
static const lean_array_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "result type of "};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " is not one of "};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "go"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkBRecOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mkBRecOn"};
static const lean_object* l_Lean_mkBRecOn___closed__0 = (const lean_object*)&l_Lean_mkBRecOn___closed__0_value;
static const lean_ctor_object l_Lean_mkBRecOn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkBRecOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkBRecOn___closed__1_value_aux_0),((lean_object*)&l_Lean_mkBRecOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 5, 240, 19, 65, 164, 203, 201)}};
static const lean_object* l_Lean_mkBRecOn___closed__1 = (const lean_object*)&l_Lean_mkBRecOn___closed__1_value;
static lean_once_cell_t l_Lean_mkBRecOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkBRecOn___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BRecOn"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 159, 21, 145, 161, 36, 75, 158)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 178, 56, 13, 18, 89, 120, 145)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 46, 193, 47, 94, 40, 114, 249)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 76, 193, 246, 60, 45, 42, 123)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(163, 74, 143, 206, 252, 62, 49, 170)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(238, 161, 3, 17, 172, 107, 105, 23)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 157, 106, 195, 120, 158, 168, 97)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(212, 17, 66, 247, 186, 244, 193, 203)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 36, 236, 78, 201, 65, 143, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = 0;
v___x_29_ = lean_box(0);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_28_, v___x_29_, v_type_19_, v___f_27_, v_cleanupAnnotations_21_, v___x_28_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___boxed(lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_cleanupAnnotations_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; lean_object* v_res_56_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_49_);
v_res_56_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_47_, v_k_48_, v_cleanupAnnotations_boxed_55_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(lean_object* v_00_u03b1_57_, lean_object* v_type_58_, lean_object* v_k_59_, uint8_t v_cleanupAnnotations_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_58_, v_k_59_, v_cleanupAnnotations_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___boxed(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_k_69_, lean_object* v_cleanupAnnotations_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_76_; lean_object* v_res_77_; 
v_cleanupAnnotations_boxed_76_ = lean_unbox(v_cleanupAnnotations_70_);
v_res_77_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(v_00_u03b1_67_, v_type_68_, v_k_69_, v_cleanupAnnotations_boxed_76_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(lean_object* v_rlvl_78_, uint8_t v___x_79_, lean_object* v_args_80_, lean_object* v_x_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; 
v___x_87_ = l_Lean_Expr_sort___override(v_rlvl_78_);
v___x_88_ = 0;
v___x_89_ = 1;
v___x_90_ = l_Lean_Meta_mkForallFVars(v_args_80_, v___x_87_, v___x_88_, v___x_79_, v___x_79_, v___x_89_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed(lean_object* v_rlvl_91_, lean_object* v___x_92_, lean_object* v_args_93_, lean_object* v_x_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v___x_1875__boxed_100_; lean_object* v_res_101_; 
v___x_1875__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_1875__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec_ref(v_x_94_);
lean_dec_ref(v_args_93_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(lean_object* v_k_102_, lean_object* v_b_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
v___x_109_ = lean_apply_6(v_k_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(v_k_110_, v_b_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(lean_object* v_name_118_, uint8_t v_bi_119_, lean_object* v_type_120_, lean_object* v_k_121_, uint8_t v_kind_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_128_, 0, v_k_121_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_118_, v_bi_119_, v_type_120_, v___f_128_, v_kind_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_129_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_129_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___boxed(lean_object* v_name_146_, lean_object* v_bi_147_, lean_object* v_type_148_, lean_object* v_k_149_, lean_object* v_kind_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_bi_boxed_156_; uint8_t v_kind_boxed_157_; lean_object* v_res_158_; 
v_bi_boxed_156_ = lean_unbox(v_bi_147_);
v_kind_boxed_157_ = lean_unbox(v_kind_150_);
v_res_158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_146_, v_bi_boxed_156_, v_type_148_, v_k_149_, v_kind_boxed_157_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(lean_object* v_name_159_, lean_object* v_type_160_, lean_object* v_k_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = 0;
v___x_168_ = 0;
v___x_169_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_159_, v___x_167_, v_type_160_, v_k_161_, v___x_168_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg___boxed(lean_object* v_name_170_, lean_object* v_type_171_, lean_object* v_k_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_name_170_, v_type_171_, v_k_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(lean_object* v_a_179_, lean_object* v_as_180_, size_t v_i_181_, size_t v_stop_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = lean_usize_dec_eq(v_i_181_, v_stop_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_array_uget_borrowed(v_as_180_, v_i_181_);
v___x_185_ = lean_expr_eqv(v_a_179_, v___x_184_);
if (v___x_185_ == 0)
{
size_t v___x_186_; size_t v___x_187_; 
v___x_186_ = ((size_t)1ULL);
v___x_187_ = lean_usize_add(v_i_181_, v___x_186_);
v_i_181_ = v___x_187_;
goto _start;
}
else
{
return v___x_185_;
}
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_a_190_, lean_object* v_as_191_, lean_object* v_i_192_, lean_object* v_stop_193_){
_start:
{
size_t v_i_boxed_194_; size_t v_stop_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_i_boxed_194_ = lean_unbox_usize(v_i_192_);
lean_dec(v_i_192_);
v_stop_boxed_195_ = lean_unbox_usize(v_stop_193_);
lean_dec(v_stop_193_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_190_, v_as_191_, v_i_boxed_194_, v_stop_boxed_195_);
lean_dec_ref(v_as_191_);
lean_dec_ref(v_a_190_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(lean_object* v_as_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_array_get_size(v_as_198_);
v___x_202_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
return v___x_202_;
}
else
{
if (v___x_202_ == 0)
{
return v___x_202_;
}
else
{
size_t v___x_203_; size_t v___x_204_; uint8_t v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_201_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_199_, v_as_198_, v___x_203_, v___x_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0___boxed(lean_object* v_as_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(v_as_206_, v_a_207_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_as_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(lean_object* v_arg__args_210_, lean_object* v_arg__type_211_, uint8_t v___x_212_, uint8_t v___x_213_, lean_object* v_prods_214_, lean_object* v_rlvl_215_, lean_object* v_motives_216_, lean_object* v_tail_217_, lean_object* v_arg_x27_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref(v_arg_x27_218_);
v___x_224_ = l_Lean_mkAppN(v_arg_x27_218_, v_arg__args_210_);
v___x_225_ = l_Lean_Meta_mkPProd(v_arg__type_211_, v___x_224_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; uint8_t v___x_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = 1;
v___x_228_ = l_Lean_Meta_mkForallFVars(v_arg__args_210_, v_a_226_, v___x_212_, v___x_213_, v___x_213_, v___x_227_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = lean_array_push(v_prods_214_, v_a_229_);
v___x_231_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_215_, v_motives_216_, v___x_230_, v_tail_217_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_array_push(v___x_234_, v_arg_x27_218_);
v___x_236_ = l_Lean_Meta_mkLambdaFVars(v___x_235_, v_a_232_, v___x_212_, v___x_213_, v___x_212_, v___x_213_, v___x_227_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec_ref(v___x_235_);
return v___x_236_;
}
else
{
lean_dec_ref(v_arg_x27_218_);
return v___x_231_;
}
}
else
{
lean_dec_ref(v_arg_x27_218_);
lean_dec(v_tail_217_);
lean_dec_ref(v_motives_216_);
lean_dec(v_rlvl_215_);
lean_dec_ref(v_prods_214_);
return v___x_228_;
}
}
else
{
lean_dec_ref(v_arg_x27_218_);
lean_dec(v_tail_217_);
lean_dec_ref(v_motives_216_);
lean_dec(v_rlvl_215_);
lean_dec_ref(v_prods_214_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed(lean_object* v_arg__args_237_, lean_object* v_arg__type_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v_prods_241_, lean_object* v_rlvl_242_, lean_object* v_motives_243_, lean_object* v_tail_244_, lean_object* v_arg_x27_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___x_2030__boxed_251_; uint8_t v___x_2031__boxed_252_; lean_object* v_res_253_; 
v___x_2030__boxed_251_ = lean_unbox(v___x_239_);
v___x_2031__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2030__boxed_251_, v___x_2031__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_arg__args_237_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(lean_object* v_motives_254_, lean_object* v_rlvl_255_, lean_object* v_prods_256_, lean_object* v_tail_257_, lean_object* v_head_258_, lean_object* v_a_259_, lean_object* v_arg__args_260_, lean_object* v_arg__type_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; uint8_t v___x_268_; uint8_t v___x_269_; 
v___x_267_ = l_Lean_Expr_getAppFn(v_arg__type_261_);
v___x_268_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(v_motives_254_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = 1;
if (v___x_268_ == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v_arg__type_261_);
lean_dec_ref(v_arg__args_260_);
lean_dec_ref(v_a_259_);
v___x_270_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_255_, v_motives_254_, v_prods_256_, v_tail_257_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_274_ = lean_array_push(v___x_273_, v_head_258_);
v___x_275_ = 1;
v___x_276_ = l_Lean_Meta_mkLambdaFVars(v___x_274_, v_a_271_, v___x_268_, v___x_269_, v___x_268_, v___x_269_, v___x_275_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec_ref(v___x_274_);
return v___x_276_;
}
else
{
lean_dec_ref(v_head_258_);
return v___x_270_;
}
}
else
{
lean_object* v___x_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_box(v___x_269_);
lean_inc(v_rlvl_255_);
v___f_278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_278_, 0, v_rlvl_255_);
lean_closure_set(v___f_278_, 1, v___x_277_);
v___x_279_ = l_Lean_Expr_fvarId_x21(v_head_258_);
lean_dec_ref(v_head_258_);
v___x_280_ = l_Lean_FVarId_getUserName___redArg(v___x_279_, v___y_262_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___f_285_; lean_object* v___x_286_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = 0;
v___x_283_ = lean_box(v___x_282_);
v___x_284_ = lean_box(v___x_269_);
v___f_285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_285_, 0, v_arg__args_260_);
lean_closure_set(v___f_285_, 1, v_arg__type_261_);
lean_closure_set(v___f_285_, 2, v___x_283_);
lean_closure_set(v___f_285_, 3, v___x_284_);
lean_closure_set(v___f_285_, 4, v_prods_256_);
lean_closure_set(v___f_285_, 5, v_rlvl_255_);
lean_closure_set(v___f_285_, 6, v_motives_254_);
lean_closure_set(v___f_285_, 7, v_tail_257_);
v___x_286_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_259_, v___f_278_, v___x_282_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_281_, v_a_287_, v___f_285_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_288_;
}
else
{
lean_dec_ref(v___f_285_);
lean_dec(v_a_281_);
return v___x_286_;
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v___f_278_);
lean_dec_ref(v_arg__type_261_);
lean_dec_ref(v_arg__args_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_tail_257_);
lean_dec_ref(v_prods_256_);
lean_dec(v_rlvl_255_);
lean_dec_ref(v_motives_254_);
v_a_289_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_280_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_280_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2___boxed(lean_object* v_motives_297_, lean_object* v_rlvl_298_, lean_object* v_prods_299_, lean_object* v_tail_300_, lean_object* v_head_301_, lean_object* v_a_302_, lean_object* v_arg__args_303_, lean_object* v_arg__type_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(v_motives_297_, v_rlvl_298_, v_prods_299_, v_tail_300_, v_head_301_, v_a_302_, v_arg__args_303_, v_arg__type_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(lean_object* v_rlvl_311_, lean_object* v_motives_312_, lean_object* v_prods_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
if (lean_obj_tag(v_a_314_) == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v_motives_312_);
v___x_320_ = l_Lean_Meta_PProdN_pack(v_rlvl_311_, v_prods_313_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_320_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_323_; 
v_head_321_ = lean_ctor_get(v_a_314_, 0);
lean_inc_n(v_head_321_, 2);
v_tail_322_ = lean_ctor_get(v_a_314_, 1);
lean_inc(v_tail_322_);
lean_dec_ref_known(v_a_314_, 2);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
v___x_323_ = lean_infer_type(v_head_321_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___f_325_; uint8_t v___x_326_; lean_object* v___x_327_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc_n(v_a_324_, 2);
lean_dec_ref_known(v___x_323_, 1);
v___f_325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2___boxed), 13, 6);
lean_closure_set(v___f_325_, 0, v_motives_312_);
lean_closure_set(v___f_325_, 1, v_rlvl_311_);
lean_closure_set(v___f_325_, 2, v_prods_313_);
lean_closure_set(v___f_325_, 3, v_tail_322_);
lean_closure_set(v___f_325_, 4, v_head_321_);
lean_closure_set(v___f_325_, 5, v_a_324_);
v___x_326_ = 0;
v___x_327_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_324_, v___f_325_, v___x_326_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_327_;
}
else
{
lean_dec(v_tail_322_);
lean_dec(v_head_321_);
lean_dec_ref(v_prods_313_);
lean_dec_ref(v_motives_312_);
lean_dec(v_rlvl_311_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___boxed(lean_object* v_rlvl_328_, lean_object* v_motives_329_, lean_object* v_prods_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_328_, v_motives_329_, v_prods_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(lean_object* v_00_u03b1_338_, lean_object* v_name_339_, uint8_t v_bi_340_, lean_object* v_type_341_, lean_object* v_k_342_, uint8_t v_kind_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_339_, v_bi_340_, v_type_341_, v_k_342_, v_kind_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_350_, lean_object* v_name_351_, lean_object* v_bi_352_, lean_object* v_type_353_, lean_object* v_k_354_, lean_object* v_kind_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_bi_boxed_361_; uint8_t v_kind_boxed_362_; lean_object* v_res_363_; 
v_bi_boxed_361_ = lean_unbox(v_bi_352_);
v_kind_boxed_362_ = lean_unbox(v_kind_355_);
v_res_363_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(v_00_u03b1_350_, v_name_351_, v_bi_boxed_361_, v_type_353_, v_k_354_, v_kind_boxed_362_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(lean_object* v_00_u03b1_364_, lean_object* v_name_365_, lean_object* v_type_366_, lean_object* v_k_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_name_365_, v_type_366_, v_k_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___boxed(lean_object* v_00_u03b1_374_, lean_object* v_name_375_, lean_object* v_type_376_, lean_object* v_k_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(v_00_u03b1_374_, v_name_375_, v_type_376_, v_k_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(lean_object* v_rlvl_386_, lean_object* v_motives_387_, lean_object* v_minor__args_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_396_ = lean_array_to_list(v_minor__args_388_);
v___x_397_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_386_, v_motives_387_, v___x_395_, v___x_396_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___boxed(lean_object* v_rlvl_398_, lean_object* v_motives_399_, lean_object* v_minor__args_400_, lean_object* v_x_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(v_rlvl_398_, v_motives_399_, v_minor__args_400_, v_x_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec_ref(v_x_401_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(lean_object* v_rlvl_408_, lean_object* v_motives_409_, lean_object* v_minorType_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___f_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v___f_416_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___boxed), 9, 2);
lean_closure_set(v___f_416_, 0, v_rlvl_408_);
lean_closure_set(v___f_416_, 1, v_motives_409_);
v___x_417_ = 0;
v___x_418_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_410_, v___f_416_, v___x_417_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___boxed(lean_object* v_rlvl_419_, lean_object* v_motives_420_, lean_object* v_minorType_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v_rlvl_419_, v_motives_420_, v_minorType_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_4921__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_4921__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_4921__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___boxed(lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(lean_object* v_name_445_, lean_object* v_levelParams_446_, lean_object* v_type_447_, lean_object* v_value_448_, lean_object* v_hints_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; uint8_t v___y_454_; uint8_t v___y_461_; lean_object* v_env_464_; uint8_t v___x_465_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_env_464_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref_n(v_env_464_, 2);
lean_dec(v___x_452_);
v___x_465_ = l_Lean_Environment_hasUnsafe(v_env_464_, v_type_447_);
if (v___x_465_ == 0)
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Environment_hasUnsafe(v_env_464_, v_value_448_);
v___y_461_ = v___x_466_;
goto v___jp_460_;
}
else
{
lean_dec_ref(v_env_464_);
v___y_461_ = v___x_465_;
goto v___jp_460_;
}
v___jp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_inc(v_name_445_);
v___x_455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_455_, 0, v_name_445_);
lean_ctor_set(v___x_455_, 1, v_levelParams_446_);
lean_ctor_set(v___x_455_, 2, v_type_447_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_457_, 0, v_name_445_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_458_, 0, v___x_455_);
lean_ctor_set(v___x_458_, 1, v_value_448_);
lean_ctor_set(v___x_458_, 2, v_hints_449_);
lean_ctor_set(v___x_458_, 3, v___x_457_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*4, v___y_454_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
v___jp_460_:
{
if (v___y_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 1;
v___y_454_ = v___x_462_;
goto v___jp_453_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
v___y_454_ = v___x_463_;
goto v___jp_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg___boxed(lean_object* v_name_467_, lean_object* v_levelParams_468_, lean_object* v_type_469_, lean_object* v_value_470_, lean_object* v_hints_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_467_, v_levelParams_468_, v_type_469_, v_value_470_, v_hints_471_, v___y_472_);
lean_dec(v___y_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(lean_object* v_name_475_, lean_object* v_levelParams_476_, lean_object* v_type_477_, lean_object* v_value_478_, lean_object* v_hints_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_475_, v_levelParams_476_, v_type_477_, v_value_478_, v_hints_479_, v___y_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___boxed(lean_object* v_name_486_, lean_object* v_levelParams_487_, lean_object* v_type_488_, lean_object* v_value_489_, lean_object* v_hints_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(v_name_486_, v_levelParams_487_, v_type_488_, v_value_489_, v_hints_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v_as_499_, size_t v_sz_500_, size_t v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_501_, v_sz_500_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v___x_498_);
lean_dec(v___x_497_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_b_502_);
return v___x_509_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_array_uget_borrowed(v_as_499_, v_i_501_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v_a_510_);
v___x_511_ = lean_infer_type(v_a_510_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
lean_inc_ref(v___x_498_);
lean_inc(v___x_497_);
v___x_513_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v___x_497_, v___x_498_, v_a_512_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; size_t v___x_516_; size_t v___x_517_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_Expr_app___override(v_b_502_, v_a_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_501_, v___x_516_);
v_i_501_ = v___x_517_;
v_b_502_ = v___x_515_;
goto _start;
}
else
{
lean_dec_ref(v_b_502_);
lean_dec_ref(v___x_498_);
lean_dec(v___x_497_);
return v___x_513_;
}
}
else
{
lean_dec_ref(v_b_502_);
lean_dec_ref(v___x_498_);
lean_dec(v___x_497_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4___boxed(lean_object* v___x_519_, lean_object* v___x_520_, lean_object* v_as_521_, lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_sz_boxed_530_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_531_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_519_, v___x_520_, v_as_521_, v_sz_boxed_530_, v_i_boxed_531_, v_b_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec_ref(v_as_521_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(lean_object* v___x_533_, uint8_t v___x_534_, lean_object* v_targs_535_, lean_object* v_x_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; uint8_t v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; 
v___x_542_ = l_Lean_Expr_sort___override(v___x_533_);
v___x_543_ = 0;
v___x_544_ = 1;
v___x_545_ = l_Lean_Meta_mkLambdaFVars(v_targs_535_, v___x_542_, v___x_543_, v___x_534_, v___x_543_, v___x_534_, v___x_544_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed(lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v_targs_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_9031__boxed_555_; lean_object* v_res_556_; 
v___x_9031__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9031__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_x_549_);
lean_dec_ref(v_targs_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_as_560_, size_t v_sz_561_, size_t v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_lt(v_i_562_, v_sz_561_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
lean_dec(v___x_557_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v_b_563_);
return v___x_570_;
}
else
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___f_573_; lean_object* v_a_574_; lean_object* v___x_575_; 
v___x_571_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
v___x_572_ = lean_box(v___x_571_);
lean_inc(v___x_557_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_573_, 0, v___x_557_);
lean_closure_set(v___f_573_, 1, v___x_572_);
v_a_574_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v_a_574_);
v___x_575_ = lean_infer_type(v_a_574_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = 0;
v___x_578_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_576_, v___f_573_, v___x_577_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; size_t v___x_581_; size_t v___x_582_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = l_Lean_Expr_app___override(v_b_563_, v_a_579_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = lean_usize_add(v_i_562_, v___x_581_);
v_i_562_ = v___x_582_;
v_b_563_ = v___x_580_;
goto _start;
}
else
{
lean_dec_ref(v_b_563_);
lean_dec(v___x_557_);
return v___x_578_;
}
}
else
{
lean_dec_ref(v___f_573_);
lean_dec_ref(v_b_563_);
lean_dec(v___x_557_);
return v___x_575_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_as_587_, lean_object* v_sz_588_, lean_object* v_i_589_, lean_object* v_b_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
size_t v_sz_boxed_596_; size_t v_i_boxed_597_; lean_object* v_res_598_; 
v_sz_boxed_596_ = lean_unbox_usize(v_sz_588_);
lean_dec(v_sz_588_);
v_i_boxed_597_ = lean_unbox_usize(v_i_589_);
lean_dec(v_i_589_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_584_, v___x_585_, v___x_586_, v_as_587_, v_sz_boxed_596_, v_i_boxed_597_, v_b_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v_as_587_);
lean_dec(v___x_586_);
lean_dec(v___x_585_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(lean_object* v_msgData_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_605_; lean_object* v_env_606_; uint8_t v___x_607_; lean_object* v_env_608_; lean_object* v___x_609_; lean_object* v_toCold_610_; lean_object* v_mctx_611_; lean_object* v_lctx_612_; lean_object* v_options_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v___x_607_ = 0;
v_env_608_ = l_Lean_Environment_setRecordingDeps(v_env_606_, v___x_607_);
v___x_609_ = lean_st_ref_get(v___y_601_);
v_toCold_610_ = lean_ctor_get(v___y_602_, 0);
v_mctx_611_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_mctx_611_);
lean_dec(v___x_609_);
v_lctx_612_ = lean_ctor_get(v___y_600_, 2);
v_options_613_ = lean_ctor_get(v_toCold_610_, 2);
lean_inc_ref(v_options_613_);
lean_inc_ref(v_lctx_612_);
v___x_614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_614_, 0, v_env_608_);
lean_ctor_set(v___x_614_, 1, v_mctx_611_);
lean_ctor_set(v___x_614_, 2, v_lctx_612_);
lean_ctor_set(v___x_614_, 3, v_options_613_);
v___x_615_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_msgData_599_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_ref_630_; lean_object* v___x_631_; lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_640_; 
v_ref_630_ = lean_ctor_get(v___y_627_, 2);
v___x_631_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_640_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_640_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
lean_inc(v_ref_630_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v_ref_630_);
lean_ctor_set(v___x_636_, 1, v_a_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set_tag(v___x_634_, 1);
lean_ctor_set(v___x_634_, 0, v___x_636_);
v___x_638_ = v___x_634_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_652_ = lean_unsigned_to_nat(4u);
v___x_653_ = lean_unsigned_to_nat(68u);
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_663_, lean_object* v_numMotives_664_, lean_object* v_numMinors_665_, lean_object* v___x_666_, lean_object* v_head_667_, lean_object* v_tail_668_, lean_object* v_recName_669_, lean_object* v_belowName_670_, lean_object* v_levelParams_671_, lean_object* v_refArgs_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_679_ = lean_nat_add(v_nParams_663_, v_numMotives_664_);
v___x_680_ = lean_nat_add(v___x_679_, v_numMinors_665_);
v___x_681_ = lean_array_get_size(v_refArgs_672_);
v___x_682_ = lean_nat_dec_lt(v___x_680_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v_refArgs_672_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
lean_dec(v_recName_669_);
lean_dec(v_tail_668_);
lean_dec(v_head_667_);
lean_dec(v_nParams_663_);
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_684_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_683_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_684_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_685_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_663_);
lean_inc_ref_n(v_refArgs_672_, 4);
v___x_686_ = l_Array_toSubarray___redArg(v_refArgs_672_, v___x_685_, v_nParams_663_);
v___x_687_ = l_Subarray_copy___redArg(v___x_686_);
lean_inc(v___x_679_);
v___x_688_ = l_Array_toSubarray___redArg(v_refArgs_672_, v_nParams_663_, v___x_679_);
v___x_689_ = l_Subarray_copy___redArg(v___x_688_);
lean_inc_n(v___x_680_, 2);
v___x_690_ = l_Array_toSubarray___redArg(v_refArgs_672_, v___x_679_, v___x_680_);
v___x_691_ = l_Subarray_copy___redArg(v___x_690_);
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = lean_nat_sub(v___x_681_, v___x_692_);
lean_inc(v___x_693_);
v___x_694_ = l_Array_toSubarray___redArg(v_refArgs_672_, v___x_680_, v___x_693_);
v___x_695_ = l_Subarray_copy___redArg(v___x_694_);
v___x_696_ = lean_array_get(v___x_666_, v_refArgs_672_, v___x_693_);
lean_dec(v___x_693_);
lean_dec_ref(v_refArgs_672_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___x_696_);
v___x_697_ = lean_infer_type(v___x_696_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
v___x_699_ = lean_infer_type(v_a_698_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_Meta_typeFormerTypeLevel(v_a_700_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
if (lean_obj_tag(v_a_702_) == 1)
{
lean_object* v_val_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; size_t v_sz_709_; size_t v___x_710_; lean_object* v___x_711_; 
v_val_703_ = lean_ctor_get(v_a_702_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v_a_702_, 1);
v___x_704_ = l_Lean_mkLevelMax(v_val_703_, v_head_667_);
lean_inc_n(v___x_704_, 2);
v___x_705_ = l_Lean_Level_succ___override(v___x_704_);
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v_tail_668_);
v___x_707_ = l_Lean_Expr_const___override(v_recName_669_, v___x_706_);
v___x_708_ = l_Lean_mkAppN(v___x_707_, v___x_687_);
v_sz_709_ = lean_array_size(v___x_689_);
v___x_710_ = ((size_t)0ULL);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_704_, v___x_680_, v___x_681_, v___x_689_, v_sz_709_, v___x_710_, v___x_708_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v___x_680_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; size_t v_sz_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v_sz_713_ = lean_array_size(v___x_691_);
lean_inc_ref(v___x_689_);
lean_inc(v___x_704_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_704_, v___x_689_, v___x_691_, v_sz_713_, v___x_710_, v_a_712_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec_ref(v___x_691_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_mkAppN(v_a_715_, v___x_695_);
lean_inc(v___x_696_);
v___x_717_ = l_Lean_Expr_app___override(v___x_716_, v___x_696_);
v___x_718_ = l_Array_append___redArg(v___x_687_, v___x_689_);
lean_dec_ref(v___x_689_);
v___x_719_ = l_Array_append___redArg(v___x_718_, v___x_695_);
lean_dec_ref(v___x_695_);
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_692_);
v___x_721_ = lean_array_push(v___x_720_, v___x_696_);
v___x_722_ = l_Array_append___redArg(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Lean_Expr_sort___override(v___x_704_);
v___x_724_ = 0;
v___x_725_ = 1;
v___x_726_ = l_Lean_Meta_mkForallFVars(v___x_722_, v___x_723_, v___x_724_, v___x_682_, v___x_682_, v___x_725_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = l_Lean_Meta_mkLambdaFVars(v___x_722_, v___x_717_, v___x_724_, v___x_682_, v___x_724_, v___x_682_, v___x_725_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec_ref(v___x_722_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_box(1);
v___x_731_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_670_, v_levelParams_671_, v_a_727_, v_a_729_, v___x_730_, v___y_677_);
return v___x_731_;
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_727_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
v_a_732_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_728_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_722_);
lean_dec_ref(v___x_717_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
v_a_740_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_726_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_726_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v___x_704_);
lean_dec(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
v_a_748_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_714_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_714_);
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
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___x_704_);
lean_dec(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
v_a_756_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_711_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_711_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec(v_a_702_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v___x_680_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
lean_dec(v_recName_669_);
lean_dec(v_tail_668_);
lean_dec(v_head_667_);
v___x_764_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_765_ = l_Lean_MessageData_ofExpr(v___x_696_);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___x_769_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_768_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
return v___x_769_;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v___x_680_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
lean_dec(v_recName_669_);
lean_dec(v_tail_668_);
lean_dec(v_head_667_);
v_a_770_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_701_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_701_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v___x_680_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
lean_dec(v_recName_669_);
lean_dec(v_tail_668_);
lean_dec(v_head_667_);
v_a_778_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_699_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_699_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec(v___x_680_);
lean_dec(v_levelParams_671_);
lean_dec(v_belowName_670_);
lean_dec(v_recName_669_);
lean_dec(v_tail_668_);
lean_dec(v_head_667_);
v_a_786_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_697_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_697_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_794_, lean_object* v_numMotives_795_, lean_object* v_numMinors_796_, lean_object* v___x_797_, lean_object* v_head_798_, lean_object* v_tail_799_, lean_object* v_recName_800_, lean_object* v_belowName_801_, lean_object* v_levelParams_802_, lean_object* v_refArgs_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_794_, v_numMotives_795_, v_numMinors_796_, v___x_797_, v_head_798_, v_tail_799_, v_recName_800_, v_belowName_801_, v_levelParams_802_, v_refArgs_803_, v_x_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec_ref(v_x_804_);
lean_dec_ref(v___x_797_);
lean_dec(v_numMinors_796_);
lean_dec(v_numMotives_795_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
if (lean_obj_tag(v_a_811_) == 0)
{
lean_object* v___x_813_; 
v___x_813_ = l_List_reverse___redArg(v_a_812_);
return v___x_813_;
}
else
{
lean_object* v_head_814_; lean_object* v_tail_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_824_; 
v_head_814_ = lean_ctor_get(v_a_811_, 0);
v_tail_815_ = lean_ctor_get(v_a_811_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_a_811_);
if (v_isSharedCheck_824_ == 0)
{
v___x_817_ = v_a_811_;
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_tail_815_);
lean_inc(v_head_814_);
lean_dec(v_a_811_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_824_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_Level_param___override(v_head_814_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 1, v_a_812_);
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_812_);
v___x_821_ = v_reuseFailAlloc_823_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
v_a_811_ = v_tail_815_;
v_a_812_ = v___x_821_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_825_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_831_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
lean_ctor_set(v___x_831_, 3, v___x_830_);
lean_ctor_set(v___x_831_, 4, v___x_830_);
lean_ctor_set(v___x_831_, 5, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_832_, uint8_t v_s_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; lean_object* v_nextMacroScope_839_; lean_object* v_ngen_840_; lean_object* v_auxDeclNGen_841_; lean_object* v_traceState_842_; lean_object* v_recordedDeps_843_; lean_object* v_messages_844_; lean_object* v_infoState_845_; lean_object* v_snapshotTasks_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_875_; 
v___x_837_ = lean_st_ref_take(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
v_nextMacroScope_839_ = lean_ctor_get(v___x_837_, 1);
v_ngen_840_ = lean_ctor_get(v___x_837_, 2);
v_auxDeclNGen_841_ = lean_ctor_get(v___x_837_, 3);
v_traceState_842_ = lean_ctor_get(v___x_837_, 4);
v_recordedDeps_843_ = lean_ctor_get(v___x_837_, 6);
v_messages_844_ = lean_ctor_get(v___x_837_, 7);
v_infoState_845_ = lean_ctor_get(v___x_837_, 8);
v_snapshotTasks_846_ = lean_ctor_get(v___x_837_, 9);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; 
v_unused_876_ = lean_ctor_get(v___x_837_, 5);
lean_dec(v_unused_876_);
v___x_848_ = v___x_837_;
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_snapshotTasks_846_);
lean_inc(v_infoState_845_);
lean_inc(v_messages_844_);
lean_inc(v_recordedDeps_843_);
lean_inc(v_traceState_842_);
lean_inc(v_auxDeclNGen_841_);
lean_inc(v_ngen_840_);
lean_inc(v_nextMacroScope_839_);
lean_inc(v_env_838_);
lean_dec(v___x_837_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_875_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_850_ = 0;
v___x_851_ = lean_box(0);
v___x_852_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_838_, v_declName_832_, v_s_833_, v___x_850_, v___x_851_);
v___x_853_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 5, v___x_853_);
lean_ctor_set(v___x_848_, 0, v___x_852_);
v___x_855_ = v___x_848_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_nextMacroScope_839_);
lean_ctor_set(v_reuseFailAlloc_874_, 2, v_ngen_840_);
lean_ctor_set(v_reuseFailAlloc_874_, 3, v_auxDeclNGen_841_);
lean_ctor_set(v_reuseFailAlloc_874_, 4, v_traceState_842_);
lean_ctor_set(v_reuseFailAlloc_874_, 5, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_874_, 6, v_recordedDeps_843_);
lean_ctor_set(v_reuseFailAlloc_874_, 7, v_messages_844_);
lean_ctor_set(v_reuseFailAlloc_874_, 8, v_infoState_845_);
lean_ctor_set(v_reuseFailAlloc_874_, 9, v_snapshotTasks_846_);
v___x_855_ = v_reuseFailAlloc_874_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_mctx_858_; lean_object* v_zetaDeltaFVarIds_859_; lean_object* v_postponed_860_; lean_object* v_diag_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_872_; 
v___x_856_ = lean_st_ref_put(v___y_835_, v___x_855_);
v___x_857_ = lean_st_ref_take(v___y_834_);
v_mctx_858_ = lean_ctor_get(v___x_857_, 0);
v_zetaDeltaFVarIds_859_ = lean_ctor_get(v___x_857_, 2);
v_postponed_860_ = lean_ctor_get(v___x_857_, 3);
v_diag_861_ = lean_ctor_get(v___x_857_, 4);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___x_857_, 1);
lean_dec(v_unused_873_);
v___x_863_ = v___x_857_;
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_diag_861_);
lean_inc(v_postponed_860_);
lean_inc(v_zetaDeltaFVarIds_859_);
lean_inc(v_mctx_858_);
lean_dec(v___x_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_872_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_box(0);
v___x_866_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_mctx_858_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_zetaDeltaFVarIds_859_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_postponed_860_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v_diag_861_);
v___x_868_ = v_reuseFailAlloc_871_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_st_ref_put(v___y_834_, v___x_868_);
v___x_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_865_);
return v___x_870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_877_, lean_object* v_s_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v_s_boxed_882_; lean_object* v_res_883_; 
v_s_boxed_882_ = lean_unbox(v_s_878_);
v_res_883_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_877_, v_s_boxed_882_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; lean_object* v___x_891_; 
v___x_890_ = 0;
v___x_891_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_884_, v___x_890_, v___y_886_, v___y_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_899_, lean_object* v_msg_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_toCold_906_; lean_object* v_currRecDepth_907_; lean_object* v_ref_908_; uint16_t v_optionFlags_909_; uint8_t v_suppressElabErrors_910_; uint8_t v_isRecordingDeps_911_; lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_toCold_906_ = lean_ctor_get(v___y_903_, 0);
v_currRecDepth_907_ = lean_ctor_get(v___y_903_, 1);
v_ref_908_ = lean_ctor_get(v___y_903_, 2);
v_optionFlags_909_ = lean_ctor_get_uint16(v___y_903_, sizeof(void*)*3);
v_suppressElabErrors_910_ = lean_ctor_get_uint8(v___y_903_, sizeof(void*)*3 + 2);
v_isRecordingDeps_911_ = lean_ctor_get_uint8(v___y_903_, sizeof(void*)*3 + 3);
v_ref_912_ = l_Lean_replaceRef(v_ref_899_, v_ref_908_);
lean_inc(v_currRecDepth_907_);
lean_inc_ref(v_toCold_906_);
v___x_913_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_913_, 0, v_toCold_906_);
lean_ctor_set(v___x_913_, 1, v_currRecDepth_907_);
lean_ctor_set(v___x_913_, 2, v_ref_912_);
lean_ctor_set_uint16(v___x_913_, sizeof(void*)*3, v_optionFlags_909_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 2, v_suppressElabErrors_910_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 3, v_isRecordingDeps_911_);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_900_, v___y_901_, v___y_902_, v___x_913_, v___y_904_);
lean_dec_ref_known(v___x_913_, 3);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_915_, lean_object* v_msg_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_915_, v_msg_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v_ref_915_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
lean_ctor_set(v___x_928_, 3, v___x_927_);
lean_ctor_set(v___x_928_, 4, v___x_926_);
lean_ctor_set(v___x_928_, 5, v___x_926_);
lean_ctor_set(v___x_928_, 6, v___x_926_);
lean_ctor_set(v___x_928_, 7, v___x_926_);
lean_ctor_set(v___x_928_, 8, v___x_926_);
lean_ctor_set(v___x_928_, 9, v___x_926_);
lean_ctor_set(v___x_928_, 10, v___x_926_);
lean_ctor_set(v___x_928_, 11, v___x_925_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_unsigned_to_nat(32u);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_932_ = ((size_t)5ULL);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_unsigned_to_nat(32u);
v___x_935_ = lean_mk_empty_array_with_capacity(v___x_934_);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_937_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
lean_ctor_set(v___x_937_, 2, v___x_933_);
lean_ctor_set(v___x_937_, 3, v___x_933_);
lean_ctor_set_usize(v___x_937_, 4, v___x_932_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_box(1);
v___x_939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_938_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_963_, lean_object* v_declHint_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v_env_969_; uint8_t v___x_970_; 
v___x_967_ = lean_box(0);
v___x_968_ = lean_st_ref_get(v___y_965_);
v_env_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc_ref(v_env_969_);
lean_dec(v___x_968_);
v___x_970_ = l_Lean_Name_isAnonymous(v_declHint_964_);
if (v___x_970_ == 0)
{
uint8_t v_isExporting_971_; 
v_isExporting_971_ = lean_ctor_get_uint8(v_env_969_, sizeof(void*)*13);
if (v_isExporting_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_964_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_msg_963_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; uint8_t v___x_974_; 
lean_inc_ref(v_env_969_);
v___x_973_ = l_Lean_Environment_setExporting(v_env_969_, v___x_970_);
lean_inc(v_declHint_964_);
lean_inc_ref(v___x_973_);
v___x_974_ = l_Lean_Environment_contains(v___x_973_, v_declHint_964_, v_isExporting_971_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_973_);
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_964_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_msg_963_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_c_981_; lean_object* v___x_982_; 
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_978_ = l_Lean_Options_empty;
v___x_979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_979_, 0, v___x_973_);
lean_ctor_set(v___x_979_, 1, v___x_976_);
lean_ctor_set(v___x_979_, 2, v___x_977_);
lean_ctor_set(v___x_979_, 3, v___x_978_);
lean_inc(v_declHint_964_);
v___x_980_ = l_Lean_MessageData_ofConstName(v_declHint_964_, v___x_970_);
v_c_981_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_981_, 0, v___x_979_);
lean_ctor_set(v_c_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_969_, v_declHint_964_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_964_);
v___x_983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_c_981_);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_MessageData_note(v___x_986_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v_msg_963_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v_val_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1024_; 
v_val_990_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_992_ = v___x_982_;
v_isShared_993_ = v_isSharedCheck_1024_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_val_990_);
lean_dec(v___x_982_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1024_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_mod_996_; uint8_t v___x_997_; 
v___x_994_ = l_Lean_Environment_header(v_env_969_);
lean_dec_ref(v_env_969_);
v___x_995_ = l_Lean_EnvironmentHeader_moduleNames(v___x_994_);
v_mod_996_ = lean_array_get(v___x_967_, v___x_995_, v_val_990_);
lean_dec(v_val_990_);
lean_dec_ref(v___x_995_);
v___x_997_ = l_Lean_isPrivateName(v_declHint_964_);
lean_dec(v_declHint_964_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v_c_981_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_MessageData_ofName(v_mod_996_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_MessageData_note(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_msg_963_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 0, v___x_1007_);
v___x_1009_ = v___x_992_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
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
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_c_981_);
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_MessageData_ofName(v_mod_996_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_MessageData_note(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_963_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 0, v___x_1020_);
v___x_1022_ = v___x_992_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
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
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_964_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_msg_963_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1026_, lean_object* v_declHint_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1026_, v_declHint_1027_, v___y_1028_);
lean_dec(v___y_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1031_, lean_object* v_declHint_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1048_; 
v___x_1038_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1031_, v_declHint_1032_, v___y_1036_);
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1048_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1043_ = l_Lean_unknownIdentifierMessageTag;
v___x_1044_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v_a_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1044_);
v___x_1046_ = v___x_1041_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1049_, lean_object* v_declHint_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1049_, v_declHint_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1057_, lean_object* v_msg_1058_, lean_object* v_declHint_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1058_, v_declHint_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1057_, v_a_1066_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1068_, lean_object* v_msg_1069_, lean_object* v_declHint_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1068_, v_msg_1069_, v_declHint_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_ref_1068_);
return v_res_1076_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1083_, lean_object* v_constName_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1090_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1091_ = 0;
lean_inc(v_constName_1084_);
v___x_1092_ = l_Lean_MessageData_ofConstName(v_constName_1084_, v___x_1091_);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1090_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1083_, v___x_1095_, v_constName_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1097_, lean_object* v_constName_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1097_, v_constName_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v_ref_1097_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; 
v_ref_1111_ = lean_ctor_get(v___y_1108_, 2);
v___x_1112_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1111_, v_constName_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v_env_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1126_ = lean_st_ref_get(v___y_1124_);
v_env_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc_ref(v_env_1127_);
lean_dec(v___x_1126_);
v___x_1128_ = 0;
lean_inc(v_constName_1120_);
v___x_1129_ = l_Lean_Environment_find_x3f(v_env_1127_, v_constName_1120_, v___x_1128_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1130_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_constName_1120_);
v_val_1131_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v___x_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1147_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1148_ = l_Lean_stringToMessageData(v___x_1147_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1155_, lean_object* v_nParams_1156_, lean_object* v_belowName_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1155_);
v___x_1164_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1155_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
if (lean_obj_tag(v_a_1165_) == 7)
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1283_; 
v_val_1166_ = lean_ctor_get(v_a_1165_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1168_ = v_a_1165_;
v_isShared_1169_ = v_isSharedCheck_1283_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v_a_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1283_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_toConstantVal_1170_; lean_object* v_numMotives_1171_; lean_object* v_numMinors_1172_; lean_object* v_levelParams_1173_; lean_object* v_type_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_toConstantVal_1170_ = lean_ctor_get(v_val_1166_, 0);
lean_inc_ref(v_toConstantVal_1170_);
v_numMotives_1171_ = lean_ctor_get(v_val_1166_, 4);
lean_inc(v_numMotives_1171_);
v_numMinors_1172_ = lean_ctor_get(v_val_1166_, 5);
lean_inc(v_numMinors_1172_);
lean_dec_ref(v_val_1166_);
v_levelParams_1173_ = lean_ctor_get(v_toConstantVal_1170_, 1);
lean_inc_n(v_levelParams_1173_, 2);
v_type_1174_ = lean_ctor_get(v_toConstantVal_1170_, 2);
lean_inc_ref(v_type_1174_);
lean_dec_ref(v_toConstantVal_1170_);
v___x_1175_ = lean_box(0);
v___x_1176_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1173_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 1)
{
lean_object* v_head_1177_; lean_object* v_tail_1178_; lean_object* v___f_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
v_head_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_head_1177_);
v_tail_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_tail_1178_);
lean_dec_ref_known(v___x_1176_, 2);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1179_, 0, v_nParams_1156_);
lean_closure_set(v___f_1179_, 1, v_numMotives_1171_);
lean_closure_set(v___f_1179_, 2, v_numMinors_1172_);
lean_closure_set(v___f_1179_, 3, v___x_1163_);
lean_closure_set(v___f_1179_, 4, v_head_1177_);
lean_closure_set(v___f_1179_, 5, v_tail_1178_);
lean_closure_set(v___f_1179_, 6, v_recName_1155_);
lean_closure_set(v___f_1179_, 7, v_belowName_1157_);
lean_closure_set(v___f_1179_, 8, v_levelParams_1173_);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1174_, v___f_1179_, v___x_1180_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_n(v_a_1182_, 2);
lean_dec_ref_known(v___x_1181_, 1);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 0, v_a_1182_);
v___x_1184_ = v___x_1168_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1182_);
v___x_1184_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_addDecl(v___x_1184_, v___x_1180_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_toConstantVal_1186_; lean_object* v_name_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref_known(v___x_1185_, 1);
v_toConstantVal_1186_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_toConstantVal_1186_);
lean_dec(v_a_1182_);
v_name_1187_ = lean_ctor_get(v_toConstantVal_1186_, 0);
lean_inc_n(v_name_1187_, 2);
lean_dec_ref(v_toConstantVal_1186_);
v___x_1188_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1187_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1267_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1266_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1266_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v_ngen_1195_; lean_object* v_auxDeclNGen_1196_; lean_object* v_traceState_1197_; lean_object* v_recordedDeps_1198_; lean_object* v_messages_1199_; lean_object* v_infoState_1200_; lean_object* v_snapshotTasks_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1264_; 
v___x_1192_ = lean_st_ref_take(v_a_1161_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1195_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1196_ = lean_ctor_get(v___x_1192_, 3);
v_traceState_1197_ = lean_ctor_get(v___x_1192_, 4);
v_recordedDeps_1198_ = lean_ctor_get(v___x_1192_, 6);
v_messages_1199_ = lean_ctor_get(v___x_1192_, 7);
v_infoState_1200_ = lean_ctor_get(v___x_1192_, 8);
v_snapshotTasks_1201_ = lean_ctor_get(v___x_1192_, 9);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1192_, 5);
lean_dec(v_unused_1265_);
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1264_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_snapshotTasks_1201_);
lean_inc(v_infoState_1200_);
lean_inc(v_messages_1199_);
lean_inc(v_recordedDeps_1198_);
lean_inc(v_traceState_1197_);
lean_inc(v_auxDeclNGen_1196_);
lean_inc(v_ngen_1195_);
lean_inc(v_nextMacroScope_1194_);
lean_inc(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1264_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc(v_name_1187_);
v___x_1205_ = l_Lean_markAuxRecursor(v_env_1193_, v_name_1187_);
v___x_1206_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 5, v___x_1206_);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1194_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1195_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1196_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1197_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_recordedDeps_1198_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_messages_1199_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_infoState_1200_);
lean_ctor_set(v_reuseFailAlloc_1263_, 9, v_snapshotTasks_1201_);
v___x_1208_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_mctx_1211_; lean_object* v_zetaDeltaFVarIds_1212_; lean_object* v_postponed_1213_; lean_object* v_diag_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1261_; 
v___x_1209_ = lean_st_ref_put(v_a_1161_, v___x_1208_);
v___x_1210_ = lean_st_ref_take(v_a_1159_);
v_mctx_1211_ = lean_ctor_get(v___x_1210_, 0);
v_zetaDeltaFVarIds_1212_ = lean_ctor_get(v___x_1210_, 2);
v_postponed_1213_ = lean_ctor_get(v___x_1210_, 3);
v_diag_1214_ = lean_ctor_get(v___x_1210_, 4);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1210_, 1);
lean_dec(v_unused_1262_);
v___x_1216_ = v___x_1210_;
v_isShared_1217_ = v_isSharedCheck_1261_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_diag_1214_);
lean_inc(v_postponed_1213_);
lean_inc(v_zetaDeltaFVarIds_1212_);
lean_inc(v_mctx_1211_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1261_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_mctx_1211_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_zetaDeltaFVarIds_1212_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_postponed_1213_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_diag_1214_);
v___x_1220_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v_nextMacroScope_1224_; lean_object* v_ngen_1225_; lean_object* v_auxDeclNGen_1226_; lean_object* v_traceState_1227_; lean_object* v_recordedDeps_1228_; lean_object* v_messages_1229_; lean_object* v_infoState_1230_; lean_object* v_snapshotTasks_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1258_; 
v___x_1221_ = lean_st_ref_put(v_a_1159_, v___x_1220_);
v___x_1222_ = lean_st_ref_take(v_a_1161_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
v_nextMacroScope_1224_ = lean_ctor_get(v___x_1222_, 1);
v_ngen_1225_ = lean_ctor_get(v___x_1222_, 2);
v_auxDeclNGen_1226_ = lean_ctor_get(v___x_1222_, 3);
v_traceState_1227_ = lean_ctor_get(v___x_1222_, 4);
v_recordedDeps_1228_ = lean_ctor_get(v___x_1222_, 6);
v_messages_1229_ = lean_ctor_get(v___x_1222_, 7);
v_infoState_1230_ = lean_ctor_get(v___x_1222_, 8);
v_snapshotTasks_1231_ = lean_ctor_get(v___x_1222_, 9);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1222_, 5);
lean_dec(v_unused_1259_);
v___x_1233_ = v___x_1222_;
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snapshotTasks_1231_);
lean_inc(v_infoState_1230_);
lean_inc(v_messages_1229_);
lean_inc(v_recordedDeps_1228_);
lean_inc(v_traceState_1227_);
lean_inc(v_auxDeclNGen_1226_);
lean_inc(v_ngen_1225_);
lean_inc(v_nextMacroScope_1224_);
lean_inc(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_addProtected(v_env_1223_, v_name_1187_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 5, v___x_1206_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1224_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1225_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1226_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1227_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_recordedDeps_1228_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_messages_1229_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_infoState_1230_);
lean_ctor_set(v_reuseFailAlloc_1257_, 9, v_snapshotTasks_1231_);
v___x_1237_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_zetaDeltaFVarIds_1241_; lean_object* v_postponed_1242_; lean_object* v_diag_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v___x_1238_ = lean_st_ref_put(v_a_1161_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v_a_1159_);
v_mctx_1240_ = lean_ctor_get(v___x_1239_, 0);
v_zetaDeltaFVarIds_1241_ = lean_ctor_get(v___x_1239_, 2);
v_postponed_1242_ = lean_ctor_get(v___x_1239_, 3);
v_diag_1243_ = lean_ctor_get(v___x_1239_, 4);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1239_, 1);
lean_dec(v_unused_1256_);
v___x_1245_ = v___x_1239_;
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_diag_1243_);
lean_inc(v_postponed_1242_);
lean_inc(v_zetaDeltaFVarIds_1241_);
lean_inc(v_mctx_1240_);
lean_dec(v___x_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1255_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_box(0);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1218_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1243_);
v___x_1249_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_st_ref_put(v_a_1159_, v___x_1249_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1247_);
v___x_1252_ = v___x_1190_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
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
lean_dec(v_a_1182_);
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1168_);
v_a_1269_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1181_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1181_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v___x_1176_);
lean_dec_ref(v_type_1174_);
lean_dec(v_levelParams_1173_);
lean_dec(v_numMinors_1172_);
lean_dec(v_numMotives_1171_);
lean_del_object(v___x_1168_);
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1278_ = l_Lean_MessageData_ofName(v_recName_1155_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1281_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1165_);
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
v___x_1284_ = l_Lean_MessageData_ofName(v_recName_1155_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1286_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
lean_dec(v_recName_1155_);
v_a_1288_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1164_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1164_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1296_, lean_object* v_nParams_1297_, lean_object* v_belowName_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1296_, v_nParams_1297_, v_belowName_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1305_, lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1313_, lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1313_, v_msg_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1321_, uint8_t v_s_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1321_, v_s_1322_, v___y_1324_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1329_, lean_object* v_s_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v_s_boxed_1336_; lean_object* v_res_1337_; 
v_s_boxed_1336_ = lean_unbox(v_s_1330_);
v_res_1337_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1329_, v_s_boxed_1336_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1338_, lean_object* v_constName_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1346_, lean_object* v_constName_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1346_, v_constName_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1354_, lean_object* v_ref_1355_, lean_object* v_constName_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1355_, v_constName_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_ref_1364_, lean_object* v_constName_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1363_, v_ref_1364_, v_constName_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v_ref_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1372_, lean_object* v_ref_1373_, lean_object* v_msg_1374_, lean_object* v_declHint_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1373_, v_msg_1374_, v_declHint_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_ref_1383_, lean_object* v_msg_1384_, lean_object* v_declHint_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1382_, v_ref_1383_, v_msg_1384_, v_declHint_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v_ref_1383_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1392_, lean_object* v_declHint_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1392_, v_declHint_1393_, v___y_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1408_, lean_object* v_ref_1409_, lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1409_, v_msg_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_ref_1418_, lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1417_, v_ref_1418_, v_msg_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v_ref_1418_);
return v_res_1425_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_unsigned_to_nat(32u);
v___x_1427_ = lean_mk_empty_array_with_capacity(v___x_1426_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((size_t)5ULL);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_unsigned_to_nat(32u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1434_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1430_);
lean_ctor_set(v___x_1434_, 3, v___x_1430_);
lean_ctor_set_usize(v___x_1434_, 4, v___x_1429_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; lean_object* v_traceState_1438_; lean_object* v_traces_1439_; lean_object* v___x_1440_; lean_object* v_traceState_1441_; lean_object* v_env_1442_; lean_object* v_nextMacroScope_1443_; lean_object* v_ngen_1444_; lean_object* v_auxDeclNGen_1445_; lean_object* v_cache_1446_; lean_object* v_recordedDeps_1447_; lean_object* v_messages_1448_; lean_object* v_infoState_1449_; lean_object* v_snapshotTasks_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1469_; 
v___x_1437_ = lean_st_ref_get(v___y_1435_);
v_traceState_1438_ = lean_ctor_get(v___x_1437_, 4);
lean_inc_ref(v_traceState_1438_);
lean_dec(v___x_1437_);
v_traces_1439_ = lean_ctor_get(v_traceState_1438_, 0);
lean_inc_ref(v_traces_1439_);
lean_dec_ref(v_traceState_1438_);
v___x_1440_ = lean_st_ref_take(v___y_1435_);
v_traceState_1441_ = lean_ctor_get(v___x_1440_, 4);
v_env_1442_ = lean_ctor_get(v___x_1440_, 0);
v_nextMacroScope_1443_ = lean_ctor_get(v___x_1440_, 1);
v_ngen_1444_ = lean_ctor_get(v___x_1440_, 2);
v_auxDeclNGen_1445_ = lean_ctor_get(v___x_1440_, 3);
v_cache_1446_ = lean_ctor_get(v___x_1440_, 5);
v_recordedDeps_1447_ = lean_ctor_get(v___x_1440_, 6);
v_messages_1448_ = lean_ctor_get(v___x_1440_, 7);
v_infoState_1449_ = lean_ctor_get(v___x_1440_, 8);
v_snapshotTasks_1450_ = lean_ctor_get(v___x_1440_, 9);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1452_ = v___x_1440_;
v_isShared_1453_ = v_isSharedCheck_1469_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_snapshotTasks_1450_);
lean_inc(v_infoState_1449_);
lean_inc(v_messages_1448_);
lean_inc(v_recordedDeps_1447_);
lean_inc(v_cache_1446_);
lean_inc(v_traceState_1441_);
lean_inc(v_auxDeclNGen_1445_);
lean_inc(v_ngen_1444_);
lean_inc(v_nextMacroScope_1443_);
lean_inc(v_env_1442_);
lean_dec(v___x_1440_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1469_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint64_t v_tid_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1467_; 
v_tid_1454_ = lean_ctor_get_uint64(v_traceState_1441_, sizeof(void*)*1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_traceState_1441_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_traceState_1441_, 0);
lean_dec(v_unused_1468_);
v___x_1456_ = v_traceState_1441_;
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v_traceState_1441_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1458_);
lean_ctor_set_uint64(v_reuseFailAlloc_1466_, sizeof(void*)*1, v_tid_1454_);
v___x_1460_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v___x_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_env_1442_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_nextMacroScope_1443_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_ngen_1444_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_auxDeclNGen_1445_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1465_, 5, v_cache_1446_);
lean_ctor_set(v_reuseFailAlloc_1465_, 6, v_recordedDeps_1447_);
lean_ctor_set(v_reuseFailAlloc_1465_, 7, v_messages_1448_);
lean_ctor_set(v_reuseFailAlloc_1465_, 8, v_infoState_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 9, v_snapshotTasks_1450_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_st_ref_put(v___y_1435_, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_traces_1439_);
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1470_);
lean_dec(v___y_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1485_, lean_object* v_opt_1486_){
_start:
{
lean_object* v_name_1487_; lean_object* v_defValue_1488_; lean_object* v_map_1489_; lean_object* v___x_1490_; 
v_name_1487_ = lean_ctor_get(v_opt_1486_, 0);
v_defValue_1488_ = lean_ctor_get(v_opt_1486_, 1);
v_map_1489_ = lean_ctor_get(v_opts_1485_, 0);
v___x_1490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1489_, v_name_1487_);
if (lean_obj_tag(v___x_1490_) == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_unbox(v_defValue_1488_);
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1490_, 1);
if (lean_obj_tag(v_val_1492_) == 1)
{
uint8_t v_v_1493_; 
v_v_1493_ = lean_ctor_get_uint8(v_val_1492_, 0);
lean_dec_ref_known(v_val_1492_, 0);
return v_v_1493_;
}
else
{
uint8_t v___x_1494_; 
lean_dec(v_val_1492_);
v___x_1494_ = lean_unbox(v_defValue_1488_);
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1495_, lean_object* v_opt_1496_){
_start:
{
uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_res_1497_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1495_, v_opt_1496_);
lean_dec_ref(v_opt_1496_);
lean_dec_ref(v_opts_1495_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = l_Lean_MessageData_ofName(v_indName_1499_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_mkBelow___lam__0(v_indName_1508_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_x_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1516_){
_start:
{
if (lean_obj_tag(v_e_1516_) == 0)
{
uint8_t v___x_1517_; 
v___x_1517_ = 2;
return v___x_1517_;
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1519_){
_start:
{
uint8_t v_res_1520_; lean_object* v_r_1521_; 
v_res_1520_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1519_);
lean_dec_ref(v_e_1519_);
v_r_1521_ = lean_box(v_res_1520_);
return v_r_1521_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v_x_1522_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1522_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v_x_1522_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v_x_1522_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 1);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
v_a_1532_ = lean_ctor_get(v_x_1522_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_x_1522_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v_x_1522_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v_x_1522_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 0);
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1540_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1543_, lean_object* v_opt_1544_){
_start:
{
lean_object* v_name_1545_; lean_object* v_defValue_1546_; lean_object* v_map_1547_; lean_object* v___x_1548_; 
v_name_1545_ = lean_ctor_get(v_opt_1544_, 0);
v_defValue_1546_ = lean_ctor_get(v_opt_1544_, 1);
v_map_1547_ = lean_ctor_get(v_opts_1543_, 0);
v___x_1548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1547_, v_name_1545_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_inc(v_defValue_1546_);
return v_defValue_1546_;
}
else
{
lean_object* v_val_1549_; 
v_val_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v___x_1548_, 1);
if (lean_obj_tag(v_val_1549_) == 3)
{
lean_object* v_v_1550_; 
v_v_1550_ = lean_ctor_get(v_val_1549_, 0);
lean_inc(v_v_1550_);
lean_dec_ref_known(v_val_1549_, 1);
return v_v_1550_;
}
else
{
lean_dec(v_val_1549_);
lean_inc(v_defValue_1546_);
return v_defValue_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1551_, lean_object* v_opt_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1551_, v_opt_1552_);
lean_dec_ref(v_opt_1552_);
lean_dec_ref(v_opts_1551_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1554_, size_t v_i_1555_, lean_object* v_bs_1556_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_usize_dec_lt(v_i_1555_, v_sz_1554_);
if (v___x_1557_ == 0)
{
return v_bs_1556_;
}
else
{
lean_object* v_v_1558_; lean_object* v_msg_1559_; lean_object* v___x_1560_; lean_object* v_bs_x27_1561_; size_t v___x_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_v_1558_ = lean_array_uget_borrowed(v_bs_1556_, v_i_1555_);
v_msg_1559_ = lean_ctor_get(v_v_1558_, 1);
lean_inc_ref(v_msg_1559_);
v___x_1560_ = lean_unsigned_to_nat(0u);
v_bs_x27_1561_ = lean_array_uset(v_bs_1556_, v_i_1555_, v___x_1560_);
v___x_1562_ = ((size_t)1ULL);
v___x_1563_ = lean_usize_add(v_i_1555_, v___x_1562_);
v___x_1564_ = lean_array_uset(v_bs_x27_1561_, v_i_1555_, v_msg_1559_);
v_i_1555_ = v___x_1563_;
v_bs_1556_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1566_, lean_object* v_i_1567_, lean_object* v_bs_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1566_);
lean_dec(v_sz_1566_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1572_, lean_object* v_data_1573_, lean_object* v_ref_1574_, lean_object* v_msg_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_toCold_1581_; lean_object* v_currRecDepth_1582_; lean_object* v_ref_1583_; uint16_t v_optionFlags_1584_; uint8_t v_suppressElabErrors_1585_; uint8_t v_isRecordingDeps_1586_; lean_object* v_ref_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_traceState_1590_; lean_object* v_traces_1591_; lean_object* v___x_1592_; size_t v_sz_1593_; size_t v___x_1594_; lean_object* v___x_1595_; lean_object* v_msg_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1636_; 
v_toCold_1581_ = lean_ctor_get(v___y_1578_, 0);
v_currRecDepth_1582_ = lean_ctor_get(v___y_1578_, 1);
v_ref_1583_ = lean_ctor_get(v___y_1578_, 2);
v_optionFlags_1584_ = lean_ctor_get_uint16(v___y_1578_, sizeof(void*)*3);
v_suppressElabErrors_1585_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1586_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 3);
v_ref_1587_ = l_Lean_replaceRef(v_ref_1574_, v_ref_1583_);
lean_inc(v_currRecDepth_1582_);
lean_inc_ref(v_toCold_1581_);
v___x_1588_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1588_, 0, v_toCold_1581_);
lean_ctor_set(v___x_1588_, 1, v_currRecDepth_1582_);
lean_ctor_set(v___x_1588_, 2, v_ref_1587_);
lean_ctor_set_uint16(v___x_1588_, sizeof(void*)*3, v_optionFlags_1584_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3 + 2, v_suppressElabErrors_1585_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3 + 3, v_isRecordingDeps_1586_);
v___x_1589_ = lean_st_ref_get(v___y_1579_);
v_traceState_1590_ = lean_ctor_get(v___x_1589_, 4);
lean_inc_ref(v_traceState_1590_);
lean_dec(v___x_1589_);
v_traces_1591_ = lean_ctor_get(v_traceState_1590_, 0);
lean_inc_ref(v_traces_1591_);
lean_dec_ref(v_traceState_1590_);
v___x_1592_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1591_);
lean_dec_ref(v_traces_1591_);
v_sz_1593_ = lean_array_size(v___x_1592_);
v___x_1594_ = ((size_t)0ULL);
v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1593_, v___x_1594_, v___x_1592_);
v_msg_1596_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1596_, 0, v_data_1573_);
lean_ctor_set(v_msg_1596_, 1, v_msg_1575_);
lean_ctor_set(v_msg_1596_, 2, v___x_1595_);
v___x_1597_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1596_, v___y_1576_, v___y_1577_, v___x_1588_, v___y_1579_);
lean_dec_ref_known(v___x_1588_, 3);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1636_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1636_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v_traceState_1603_; lean_object* v_env_1604_; lean_object* v_nextMacroScope_1605_; lean_object* v_ngen_1606_; lean_object* v_auxDeclNGen_1607_; lean_object* v_cache_1608_; lean_object* v_recordedDeps_1609_; lean_object* v_messages_1610_; lean_object* v_infoState_1611_; lean_object* v_snapshotTasks_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1635_; 
v___x_1602_ = lean_st_ref_take(v___y_1579_);
v_traceState_1603_ = lean_ctor_get(v___x_1602_, 4);
v_env_1604_ = lean_ctor_get(v___x_1602_, 0);
v_nextMacroScope_1605_ = lean_ctor_get(v___x_1602_, 1);
v_ngen_1606_ = lean_ctor_get(v___x_1602_, 2);
v_auxDeclNGen_1607_ = lean_ctor_get(v___x_1602_, 3);
v_cache_1608_ = lean_ctor_get(v___x_1602_, 5);
v_recordedDeps_1609_ = lean_ctor_get(v___x_1602_, 6);
v_messages_1610_ = lean_ctor_get(v___x_1602_, 7);
v_infoState_1611_ = lean_ctor_get(v___x_1602_, 8);
v_snapshotTasks_1612_ = lean_ctor_get(v___x_1602_, 9);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1614_ = v___x_1602_;
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_snapshotTasks_1612_);
lean_inc(v_infoState_1611_);
lean_inc(v_messages_1610_);
lean_inc(v_recordedDeps_1609_);
lean_inc(v_cache_1608_);
lean_inc(v_traceState_1603_);
lean_inc(v_auxDeclNGen_1607_);
lean_inc(v_ngen_1606_);
lean_inc(v_nextMacroScope_1605_);
lean_inc(v_env_1604_);
lean_dec(v___x_1602_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1635_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
uint64_t v_tid_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1633_; 
v_tid_1616_ = lean_ctor_get_uint64(v_traceState_1603_, sizeof(void*)*1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_traceState_1603_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; 
v_unused_1634_ = lean_ctor_get(v_traceState_1603_, 0);
lean_dec(v_unused_1634_);
v___x_1618_ = v_traceState_1603_;
v_isShared_1619_ = v_isSharedCheck_1633_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_traceState_1603_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1633_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v_ref_1574_);
lean_ctor_set(v___x_1621_, 1, v_a_1598_);
v___x_1622_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1572_, v___x_1621_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1622_);
v___x_1624_ = v___x_1618_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1622_);
lean_ctor_set_uint64(v_reuseFailAlloc_1632_, sizeof(void*)*1, v_tid_1616_);
v___x_1624_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 4, v___x_1624_);
v___x_1626_ = v___x_1614_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_env_1604_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_nextMacroScope_1605_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_ngen_1606_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_auxDeclNGen_1607_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1631_, 5, v_cache_1608_);
lean_ctor_set(v_reuseFailAlloc_1631_, 6, v_recordedDeps_1609_);
lean_ctor_set(v_reuseFailAlloc_1631_, 7, v_messages_1610_);
lean_ctor_set(v_reuseFailAlloc_1631_, 8, v_infoState_1611_);
lean_ctor_set(v_reuseFailAlloc_1631_, 9, v_snapshotTasks_1612_);
v___x_1626_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_st_ref_put(v___y_1579_, v___x_1626_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1620_);
v___x_1629_ = v___x_1600_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1620_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1637_, lean_object* v_data_1638_, lean_object* v_ref_1639_, lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1637_, v_data_1638_, v_ref_1639_, v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1646_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1647_; double v___x_1648_; 
v___x_1647_ = lean_unsigned_to_nat(0u);
v___x_1648_ = lean_float_of_nat(v___x_1647_);
return v___x_1648_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1651_ = l_Lean_stringToMessageData(v___x_1650_);
return v___x_1651_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1652_; double v___x_1653_; 
v___x_1652_ = lean_unsigned_to_nat(1000u);
v___x_1653_ = lean_float_of_nat(v___x_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1654_, uint8_t v_collapsed_1655_, lean_object* v_tag_1656_, lean_object* v_opts_1657_, uint8_t v_clsEnabled_1658_, lean_object* v_oldTraces_1659_, lean_object* v_msg_1660_, lean_object* v_resStartStop_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_fst_1667_; lean_object* v_snd_1668_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v_data_1672_; lean_object* v_fst_1675_; lean_object* v_snd_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___y_1680_; lean_object* v_a_1681_; uint8_t v___y_1696_; double v___y_1728_; 
v_fst_1667_ = lean_ctor_get(v_resStartStop_1661_, 0);
lean_inc(v_fst_1667_);
v_snd_1668_ = lean_ctor_get(v_resStartStop_1661_, 1);
lean_inc(v_snd_1668_);
lean_dec_ref(v_resStartStop_1661_);
v_fst_1675_ = lean_ctor_get(v_snd_1668_, 0);
lean_inc(v_fst_1675_);
v_snd_1676_ = lean_ctor_get(v_snd_1668_, 1);
lean_inc(v_snd_1676_);
lean_dec(v_snd_1668_);
v___x_1677_ = l_Lean_trace_profiler;
v___x_1678_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1657_, v___x_1677_);
if (v___x_1678_ == 0)
{
v___y_1696_ = v___x_1678_;
goto v___jp_1695_;
}
else
{
lean_object* v___x_1733_; uint8_t v___x_1734_; 
v___x_1733_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1734_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1657_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; double v___x_1737_; double v___x_1738_; double v___x_1739_; 
v___x_1735_ = l_Lean_trace_profiler_threshold;
v___x_1736_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1657_, v___x_1735_);
v___x_1737_ = lean_float_of_nat(v___x_1736_);
v___x_1738_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1739_ = lean_float_div(v___x_1737_, v___x_1738_);
v___y_1728_ = v___x_1739_;
goto v___jp_1727_;
}
else
{
lean_object* v___x_1740_; lean_object* v___x_1741_; double v___x_1742_; 
v___x_1740_ = l_Lean_trace_profiler_threshold;
v___x_1741_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1657_, v___x_1740_);
v___x_1742_ = lean_float_of_nat(v___x_1741_);
v___y_1728_ = v___x_1742_;
goto v___jp_1727_;
}
}
v___jp_1669_:
{
lean_object* v___x_1673_; 
lean_inc(v___y_1671_);
v___x_1673_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1659_, v_data_1672_, v___y_1671_, v___y_1670_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v___x_1674_; 
lean_dec_ref_known(v___x_1673_, 1);
v___x_1674_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1667_);
return v___x_1674_;
}
else
{
lean_dec(v_fst_1667_);
return v___x_1673_;
}
}
v___jp_1679_:
{
uint8_t v_result_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; double v___x_1685_; lean_object* v_data_1686_; 
v_result_1682_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1667_);
v___x_1683_ = lean_box(v_result_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
v___x_1685_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1656_);
lean_inc_ref(v___x_1684_);
lean_inc(v_cls_1654_);
v_data_1686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1686_, 0, v_cls_1654_);
lean_ctor_set(v_data_1686_, 1, v___x_1684_);
lean_ctor_set(v_data_1686_, 2, v_tag_1656_);
lean_ctor_set_float(v_data_1686_, sizeof(void*)*3, v___x_1685_);
lean_ctor_set_float(v_data_1686_, sizeof(void*)*3 + 8, v___x_1685_);
lean_ctor_set_uint8(v_data_1686_, sizeof(void*)*3 + 16, v_collapsed_1655_);
if (v___x_1678_ == 0)
{
lean_dec_ref_known(v___x_1684_, 1);
lean_dec(v_snd_1676_);
lean_dec(v_fst_1675_);
lean_dec_ref(v_tag_1656_);
lean_dec(v_cls_1654_);
v___y_1670_ = v_a_1681_;
v___y_1671_ = v___y_1680_;
v_data_1672_ = v_data_1686_;
goto v___jp_1669_;
}
else
{
lean_object* v_data_1687_; double v___x_1688_; double v___x_1689_; 
lean_dec_ref_known(v_data_1686_, 3);
v_data_1687_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1687_, 0, v_cls_1654_);
lean_ctor_set(v_data_1687_, 1, v___x_1684_);
lean_ctor_set(v_data_1687_, 2, v_tag_1656_);
v___x_1688_ = lean_unbox_float(v_fst_1675_);
lean_dec(v_fst_1675_);
lean_ctor_set_float(v_data_1687_, sizeof(void*)*3, v___x_1688_);
v___x_1689_ = lean_unbox_float(v_snd_1676_);
lean_dec(v_snd_1676_);
lean_ctor_set_float(v_data_1687_, sizeof(void*)*3 + 8, v___x_1689_);
lean_ctor_set_uint8(v_data_1687_, sizeof(void*)*3 + 16, v_collapsed_1655_);
v___y_1670_ = v_a_1681_;
v___y_1671_ = v___y_1680_;
v_data_1672_ = v_data_1687_;
goto v___jp_1669_;
}
}
v___jp_1690_:
{
lean_object* v_ref_1691_; lean_object* v___x_1692_; 
v_ref_1691_ = lean_ctor_get(v___y_1664_, 2);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v_fst_1667_);
v___x_1692_ = lean_apply_6(v_msg_1660_, v_fst_1667_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, lean_box(0));
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___y_1680_ = v_ref_1691_;
v_a_1681_ = v_a_1693_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1694_; 
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1680_ = v_ref_1691_;
v_a_1681_ = v___x_1694_;
goto v___jp_1679_;
}
}
v___jp_1695_:
{
if (v_clsEnabled_1658_ == 0)
{
if (v___y_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v_traceState_1698_; lean_object* v_env_1699_; lean_object* v_nextMacroScope_1700_; lean_object* v_ngen_1701_; lean_object* v_auxDeclNGen_1702_; lean_object* v_cache_1703_; lean_object* v_recordedDeps_1704_; lean_object* v_messages_1705_; lean_object* v_infoState_1706_; lean_object* v_snapshotTasks_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_snd_1676_);
lean_dec(v_fst_1675_);
lean_dec_ref(v_msg_1660_);
lean_dec_ref(v_tag_1656_);
lean_dec(v_cls_1654_);
v___x_1697_ = lean_st_ref_take(v___y_1665_);
v_traceState_1698_ = lean_ctor_get(v___x_1697_, 4);
v_env_1699_ = lean_ctor_get(v___x_1697_, 0);
v_nextMacroScope_1700_ = lean_ctor_get(v___x_1697_, 1);
v_ngen_1701_ = lean_ctor_get(v___x_1697_, 2);
v_auxDeclNGen_1702_ = lean_ctor_get(v___x_1697_, 3);
v_cache_1703_ = lean_ctor_get(v___x_1697_, 5);
v_recordedDeps_1704_ = lean_ctor_get(v___x_1697_, 6);
v_messages_1705_ = lean_ctor_get(v___x_1697_, 7);
v_infoState_1706_ = lean_ctor_get(v___x_1697_, 8);
v_snapshotTasks_1707_ = lean_ctor_get(v___x_1697_, 9);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1709_ = v___x_1697_;
v_isShared_1710_ = v_isSharedCheck_1726_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_snapshotTasks_1707_);
lean_inc(v_infoState_1706_);
lean_inc(v_messages_1705_);
lean_inc(v_recordedDeps_1704_);
lean_inc(v_cache_1703_);
lean_inc(v_traceState_1698_);
lean_inc(v_auxDeclNGen_1702_);
lean_inc(v_ngen_1701_);
lean_inc(v_nextMacroScope_1700_);
lean_inc(v_env_1699_);
lean_dec(v___x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1726_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
uint64_t v_tid_1711_; lean_object* v_traces_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1725_; 
v_tid_1711_ = lean_ctor_get_uint64(v_traceState_1698_, sizeof(void*)*1);
v_traces_1712_ = lean_ctor_get(v_traceState_1698_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_traceState_1698_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1714_ = v_traceState_1698_;
v_isShared_1715_ = v_isSharedCheck_1725_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_traces_1712_);
lean_dec(v_traceState_1698_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1725_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1659_, v_traces_1712_);
lean_dec_ref(v_traces_1712_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1716_);
lean_ctor_set_uint64(v_reuseFailAlloc_1724_, sizeof(void*)*1, v_tid_1711_);
v___x_1718_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 4, v___x_1718_);
v___x_1720_ = v___x_1709_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_env_1699_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_nextMacroScope_1700_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_ngen_1701_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_auxDeclNGen_1702_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_cache_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v_recordedDeps_1704_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_messages_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v_infoState_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 9, v_snapshotTasks_1707_);
v___x_1720_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1721_ = lean_st_ref_put(v___y_1665_, v___x_1720_);
v___x_1722_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1667_);
return v___x_1722_;
}
}
}
}
}
else
{
goto v___jp_1690_;
}
}
else
{
goto v___jp_1690_;
}
}
v___jp_1727_:
{
double v___x_1729_; double v___x_1730_; double v___x_1731_; uint8_t v___x_1732_; 
v___x_1729_ = lean_unbox_float(v_snd_1676_);
v___x_1730_ = lean_unbox_float(v_fst_1675_);
v___x_1731_ = lean_float_sub(v___x_1729_, v___x_1730_);
v___x_1732_ = lean_float_decLt(v___y_1728_, v___x_1731_);
v___y_1696_ = v___x_1732_;
goto v___jp_1695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1743_, lean_object* v_collapsed_1744_, lean_object* v_tag_1745_, lean_object* v_opts_1746_, lean_object* v_clsEnabled_1747_, lean_object* v_oldTraces_1748_, lean_object* v_msg_1749_, lean_object* v_resStartStop_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
uint8_t v_collapsed_boxed_1756_; uint8_t v_clsEnabled_boxed_1757_; lean_object* v_res_1758_; 
v_collapsed_boxed_1756_ = lean_unbox(v_collapsed_1744_);
v_clsEnabled_boxed_1757_ = lean_unbox(v_clsEnabled_1747_);
v_res_1758_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1743_, v_collapsed_boxed_1756_, v_tag_1745_, v_opts_1746_, v_clsEnabled_boxed_1757_, v_oldTraces_1748_, v_msg_1749_, v_resStartStop_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec_ref(v_opts_1746_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1759_, lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v_a_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_lt(v_a_1763_, v_upperBound_1759_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec(v_a_1763_);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1764_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_unsigned_to_nat(1u);
v___x_1774_ = lean_nat_add(v_a_1763_, v___x_1773_);
lean_dec(v_a_1763_);
lean_inc_n(v___x_1774_, 2);
lean_inc(v___x_1760_);
v___x_1775_ = lean_name_append_index_after(v___x_1760_, v___x_1774_);
lean_inc(v___x_1761_);
v___x_1776_ = lean_name_append_index_after(v___x_1761_, v___x_1774_);
lean_inc(v___x_1762_);
v___x_1777_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1775_, v___x_1762_, v___x_1776_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_dec_ref_known(v___x_1777_, 1);
v_a_1763_ = v___x_1774_;
v_b_1764_ = v___x_1772_;
goto _start;
}
else
{
lean_dec(v___x_1774_);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1779_, lean_object* v___x_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v_a_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1779_, v___x_1780_, v___x_1781_, v___x_1782_, v_a_1783_, v_b_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v_upperBound_1779_);
return v_res_1790_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1801_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1802_ = l_Lean_Name_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1803_; double v___x_1804_; 
v___x_1803_ = lean_unsigned_to_nat(1000000000u);
v___x_1804_ = lean_float_of_nat(v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_toCold_1811_; lean_object* v_options_1812_; lean_object* v_inheritedTraceOptions_1813_; uint8_t v_hasTrace_1814_; lean_object* v___x_1815_; 
v_toCold_1811_ = lean_ctor_get(v_a_1808_, 0);
v_options_1812_ = lean_ctor_get(v_toCold_1811_, 2);
v_inheritedTraceOptions_1813_ = lean_ctor_get(v_toCold_1811_, 11);
v_hasTrace_1814_ = lean_ctor_get_uint8(v_options_1812_, sizeof(void*)*1);
v___x_1815_ = lean_box(0);
if (v_hasTrace_1814_ == 0)
{
lean_object* v___x_1816_; 
lean_inc(v_indName_1805_);
v___x_1816_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1880_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1880_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1880_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
if (lean_obj_tag(v_a_1817_) == 5)
{
lean_object* v_val_1821_; uint8_t v_isRec_1822_; 
v_val_1821_ = lean_ctor_get(v_a_1817_, 0);
lean_inc_ref(v_val_1821_);
lean_dec_ref_known(v_a_1817_, 1);
v_isRec_1822_ = lean_ctor_get_uint8(v_val_1821_, sizeof(void*)*6);
if (v_isRec_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec_ref(v_val_1821_);
lean_dec(v_indName_1805_);
v___x_1823_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1823_);
v___x_1825_ = v___x_1819_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
else
{
lean_object* v_toConstantVal_1827_; lean_object* v_numParams_1828_; lean_object* v_all_1829_; lean_object* v_numNested_1830_; lean_object* v_type_1831_; lean_object* v___x_1832_; 
lean_del_object(v___x_1819_);
v_toConstantVal_1827_ = lean_ctor_get(v_val_1821_, 0);
lean_inc_ref(v_toConstantVal_1827_);
v_numParams_1828_ = lean_ctor_get(v_val_1821_, 1);
lean_inc(v_numParams_1828_);
v_all_1829_ = lean_ctor_get(v_val_1821_, 3);
lean_inc(v_all_1829_);
v_numNested_1830_ = lean_ctor_get(v_val_1821_, 5);
lean_inc(v_numNested_1830_);
lean_dec_ref(v_val_1821_);
v_type_1831_ = lean_ctor_get(v_toConstantVal_1827_, 2);
lean_inc_ref(v_type_1831_);
lean_dec_ref(v_toConstantVal_1827_);
v___x_1832_ = l_Lean_Meta_isPropFormerType(v_type_1831_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1867_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1867_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1867_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_del_object(v___x_1835_);
lean_inc_n(v_indName_1805_, 2);
v___x_1838_ = l_Lean_mkRecName(v_indName_1805_);
v___x_1839_ = l_Lean_mkBelowName(v_indName_1805_);
lean_inc(v___x_1839_);
lean_inc(v_numParams_1828_);
lean_inc(v___x_1838_);
v___x_1840_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1838_, v_numParams_1828_, v___x_1839_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1861_; 
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1840_, 0);
lean_dec(v_unused_1862_);
v___x_1842_ = v___x_1840_;
v_isShared_1843_ = v_isSharedCheck_1861_;
goto v_resetjp_1841_;
}
else
{
lean_dec(v___x_1840_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1861_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = l_List_get_x21Internal___redArg(v___x_1815_, v_all_1829_, v___x_1844_);
lean_dec(v_all_1829_);
v___x_1846_ = lean_name_eq(v___x_1845_, v_indName_1805_);
lean_dec(v_indName_1805_);
lean_dec(v___x_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec(v___x_1839_);
lean_dec(v___x_1838_);
lean_dec(v_numNested_1830_);
lean_dec(v_numParams_1828_);
v___x_1847_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1847_);
v___x_1849_ = v___x_1842_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_del_object(v___x_1842_);
v___x_1851_ = lean_box(0);
v___x_1852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1830_, v___x_1838_, v___x_1839_, v_numParams_1828_, v___x_1844_, v___x_1851_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_numNested_1830_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v___x_1852_, 0);
lean_dec(v_unused_1860_);
v___x_1854_ = v___x_1852_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_dec(v___x_1852_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1851_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
else
{
return v___x_1852_;
}
}
}
}
else
{
lean_dec(v___x_1839_);
lean_dec(v___x_1838_);
lean_dec(v_numNested_1830_);
lean_dec(v_all_1829_);
lean_dec(v_numParams_1828_);
lean_dec(v_indName_1805_);
return v___x_1840_;
}
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_dec(v_numNested_1830_);
lean_dec(v_all_1829_);
lean_dec(v_numParams_1828_);
lean_dec(v_indName_1805_);
v___x_1863_ = lean_box(0);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1863_);
v___x_1865_ = v___x_1835_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec(v_numNested_1830_);
lean_dec(v_all_1829_);
lean_dec(v_numParams_1828_);
lean_dec(v_indName_1805_);
v_a_1868_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1832_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1832_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
lean_dec(v_a_1817_);
lean_dec(v_indName_1805_);
v___x_1876_ = lean_box(0);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1876_);
v___x_1878_ = v___x_1819_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec(v_indName_1805_);
v_a_1881_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1816_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1816_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_a_1912_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v_a_1917_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_a_1922_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_a_1934_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v_a_1939_; 
lean_inc(v_indName_1805_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1889_, 0, v_indName_1805_);
v___x_1890_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1891_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1892_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1813_, v_options_1812_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = l_Lean_trace_profiler;
v___x_2007_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1812_, v___x_2006_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec_ref(v___f_1889_);
lean_inc(v_indName_1805_);
v___x_2008_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2072_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2072_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2072_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
if (lean_obj_tag(v_a_2009_) == 5)
{
lean_object* v_val_2013_; uint8_t v_isRec_2014_; 
v_val_2013_ = lean_ctor_get(v_a_2009_, 0);
lean_inc_ref(v_val_2013_);
lean_dec_ref_known(v_a_2009_, 1);
v_isRec_2014_ = lean_ctor_get_uint8(v_val_2013_, sizeof(void*)*6);
if (v_isRec_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_dec_ref(v_val_2013_);
lean_dec(v_indName_1805_);
v___x_2015_ = lean_box(0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2015_);
v___x_2017_ = v___x_2011_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v_toConstantVal_2019_; lean_object* v_numParams_2020_; lean_object* v_all_2021_; lean_object* v_numNested_2022_; lean_object* v_type_2023_; lean_object* v___x_2024_; 
lean_del_object(v___x_2011_);
v_toConstantVal_2019_ = lean_ctor_get(v_val_2013_, 0);
lean_inc_ref(v_toConstantVal_2019_);
v_numParams_2020_ = lean_ctor_get(v_val_2013_, 1);
lean_inc(v_numParams_2020_);
v_all_2021_ = lean_ctor_get(v_val_2013_, 3);
lean_inc(v_all_2021_);
v_numNested_2022_ = lean_ctor_get(v_val_2013_, 5);
lean_inc(v_numNested_2022_);
lean_dec_ref(v_val_2013_);
v_type_2023_ = lean_ctor_get(v_toConstantVal_2019_, 2);
lean_inc_ref(v_type_2023_);
lean_dec_ref(v_toConstantVal_2019_);
v___x_2024_ = l_Lean_Meta_isPropFormerType(v_type_2023_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2059_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2059_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2059_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_del_object(v___x_2027_);
lean_inc_n(v_indName_1805_, 2);
v___x_2030_ = l_Lean_mkRecName(v_indName_1805_);
v___x_2031_ = l_Lean_mkBelowName(v_indName_1805_);
lean_inc(v___x_2031_);
lean_inc(v_numParams_2020_);
lean_inc(v___x_2030_);
v___x_2032_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2030_, v_numParams_2020_, v___x_2031_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2053_; 
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2054_);
v___x_2034_ = v___x_2032_;
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_2032_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2053_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = l_List_get_x21Internal___redArg(v___x_1815_, v_all_2021_, v___x_2036_);
lean_dec(v_all_2021_);
v___x_2038_ = lean_name_eq(v___x_2037_, v_indName_1805_);
lean_dec(v_indName_1805_);
lean_dec(v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec(v___x_2031_);
lean_dec(v___x_2030_);
lean_dec(v_numNested_2022_);
lean_dec(v_numParams_2020_);
v___x_2039_ = lean_box(0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2039_);
v___x_2041_ = v___x_2034_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_del_object(v___x_2034_);
v___x_2043_ = lean_box(0);
v___x_2044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2022_, v___x_2030_, v___x_2031_, v_numParams_2020_, v___x_2036_, v___x_2043_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_numNested_2022_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2043_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2043_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
return v___x_2044_;
}
}
}
}
else
{
lean_dec(v___x_2031_);
lean_dec(v___x_2030_);
lean_dec(v_numNested_2022_);
lean_dec(v_all_2021_);
lean_dec(v_numParams_2020_);
lean_dec(v_indName_1805_);
return v___x_2032_;
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
lean_dec(v_numNested_2022_);
lean_dec(v_all_2021_);
lean_dec(v_numParams_2020_);
lean_dec(v_indName_1805_);
v___x_2055_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2055_);
v___x_2057_ = v___x_2027_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_numNested_2022_);
lean_dec(v_all_2021_);
lean_dec(v_numParams_2020_);
lean_dec(v_indName_1805_);
v_a_2060_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2024_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2024_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_dec(v_a_2009_);
lean_dec(v_indName_1805_);
v___x_2068_ = lean_box(0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2068_);
v___x_2070_ = v___x_2011_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
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
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_indName_1805_);
v_a_2073_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2008_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2008_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
goto v___jp_1941_;
}
}
else
{
goto v___jp_1941_;
}
v___jp_1894_:
{
lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; double v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = lean_io_mono_nanos_now();
v___x_1899_ = lean_float_of_nat(v___y_1896_);
v___x_1900_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1901_ = lean_float_div(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_float_of_nat(v___x_1898_);
v___x_1903_ = lean_float_div(v___x_1902_, v___x_1900_);
v___x_1904_ = lean_box_float(v___x_1901_);
v___x_1905_ = lean_box_float(v___x_1903_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1897_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1890_, v_hasTrace_1814_, v___x_1891_, v_options_1812_, v___x_1893_, v___y_1895_, v___f_1889_, v___x_1907_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
return v___x_1908_;
}
v___jp_1909_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1912_);
v___y_1895_ = v___y_1910_;
v___y_1896_ = v___y_1911_;
v_a_1897_ = v___x_1913_;
goto v___jp_1894_;
}
v___jp_1914_:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_a_1917_);
v___y_1895_ = v___y_1915_;
v___y_1896_ = v___y_1916_;
v_a_1897_ = v___x_1918_;
goto v___jp_1894_;
}
v___jp_1919_:
{
lean_object* v___x_1923_; double v___x_1924_; double v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1923_ = lean_io_get_num_heartbeats();
v___x_1924_ = lean_float_of_nat(v___y_1921_);
v___x_1925_ = lean_float_of_nat(v___x_1923_);
v___x_1926_ = lean_box_float(v___x_1924_);
v___x_1927_ = lean_box_float(v___x_1925_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_a_1922_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1890_, v_hasTrace_1814_, v___x_1891_, v_options_1812_, v___x_1893_, v___y_1920_, v___f_1889_, v___x_1929_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
return v___x_1930_;
}
v___jp_1931_:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1934_);
v___y_1920_ = v___y_1932_;
v___y_1921_ = v___y_1933_;
v_a_1922_ = v___x_1935_;
goto v___jp_1919_;
}
v___jp_1936_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1939_);
v___y_1920_ = v___y_1937_;
v___y_1921_ = v___y_1938_;
v_a_1922_ = v___x_1940_;
goto v___jp_1919_;
}
v___jp_1941_:
{
lean_object* v___x_1942_; lean_object* v_a_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1942_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1809_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref(v___x_1942_);
v___x_1944_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1945_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1812_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1805_);
v___x_1947_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
if (lean_obj_tag(v_a_1948_) == 5)
{
lean_object* v_val_1949_; uint8_t v_isRec_1950_; 
v_val_1949_ = lean_ctor_get(v_a_1948_, 0);
lean_inc_ref(v_val_1949_);
lean_dec_ref_known(v_a_1948_, 1);
v_isRec_1950_ = lean_ctor_get_uint8(v_val_1949_, sizeof(void*)*6);
if (v_isRec_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref(v_val_1949_);
lean_dec(v_indName_1805_);
v___x_1951_ = lean_box(0);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v___x_1951_;
goto v___jp_1909_;
}
else
{
lean_object* v_toConstantVal_1952_; lean_object* v_numParams_1953_; lean_object* v_all_1954_; lean_object* v_numNested_1955_; lean_object* v_type_1956_; lean_object* v___x_1957_; 
v_toConstantVal_1952_ = lean_ctor_get(v_val_1949_, 0);
lean_inc_ref(v_toConstantVal_1952_);
v_numParams_1953_ = lean_ctor_get(v_val_1949_, 1);
lean_inc(v_numParams_1953_);
v_all_1954_ = lean_ctor_get(v_val_1949_, 3);
lean_inc(v_all_1954_);
v_numNested_1955_ = lean_ctor_get(v_val_1949_, 5);
lean_inc(v_numNested_1955_);
lean_dec_ref(v_val_1949_);
v_type_1956_ = lean_ctor_get(v_toConstantVal_1952_, 2);
lean_inc_ref(v_type_1956_);
lean_dec_ref(v_toConstantVal_1952_);
v___x_1957_ = l_Lean_Meta_isPropFormerType(v_type_1956_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; uint8_t v___x_1959_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = lean_unbox(v_a_1958_);
lean_dec(v_a_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_inc_n(v_indName_1805_, 2);
v___x_1960_ = l_Lean_mkRecName(v_indName_1805_);
v___x_1961_ = l_Lean_mkBelowName(v_indName_1805_);
lean_inc(v___x_1961_);
lean_inc(v_numParams_1953_);
lean_inc(v___x_1960_);
v___x_1962_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1960_, v_numParams_1953_, v___x_1961_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
lean_dec_ref_known(v___x_1962_, 1);
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = l_List_get_x21Internal___redArg(v___x_1815_, v_all_1954_, v___x_1963_);
lean_dec(v_all_1954_);
v___x_1965_ = lean_name_eq(v___x_1964_, v_indName_1805_);
lean_dec(v_indName_1805_);
lean_dec(v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v___x_1961_);
lean_dec(v___x_1960_);
lean_dec(v_numNested_1955_);
lean_dec(v_numParams_1953_);
v___x_1966_ = lean_box(0);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v___x_1966_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1955_, v___x_1960_, v___x_1961_, v_numParams_1953_, v___x_1963_, v___x_1967_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_numNested_1955_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_dec_ref_known(v___x_1968_, 1);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v___x_1967_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
v___y_1915_ = v_a_1943_;
v___y_1916_ = v___x_1946_;
v_a_1917_ = v_a_1969_;
goto v___jp_1914_;
}
}
}
else
{
lean_dec(v___x_1961_);
lean_dec(v___x_1960_);
lean_dec(v_numNested_1955_);
lean_dec(v_all_1954_);
lean_dec(v_numParams_1953_);
lean_dec(v_indName_1805_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1962_, 1);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v_a_1970_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_1971_; 
v_a_1971_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1962_, 1);
v___y_1915_ = v_a_1943_;
v___y_1916_ = v___x_1946_;
v_a_1917_ = v_a_1971_;
goto v___jp_1914_;
}
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v_numNested_1955_);
lean_dec(v_all_1954_);
lean_dec(v_numParams_1953_);
lean_dec(v_indName_1805_);
v___x_1972_ = lean_box(0);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v___x_1972_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_a_1973_; 
lean_dec(v_numNested_1955_);
lean_dec(v_all_1954_);
lean_dec(v_numParams_1953_);
lean_dec(v_indName_1805_);
v_a_1973_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1957_, 1);
v___y_1915_ = v_a_1943_;
v___y_1916_ = v___x_1946_;
v_a_1917_ = v_a_1973_;
goto v___jp_1914_;
}
}
}
else
{
lean_object* v___x_1974_; 
lean_dec(v_a_1948_);
lean_dec(v_indName_1805_);
v___x_1974_ = lean_box(0);
v___y_1910_ = v_a_1943_;
v___y_1911_ = v___x_1946_;
v_a_1912_ = v___x_1974_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_a_1975_; 
lean_dec(v_indName_1805_);
v_a_1975_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1947_, 1);
v___y_1915_ = v_a_1943_;
v___y_1916_ = v___x_1946_;
v_a_1917_ = v_a_1975_;
goto v___jp_1914_;
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1805_);
v___x_1977_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
if (lean_obj_tag(v_a_1978_) == 5)
{
lean_object* v_val_1979_; uint8_t v_isRec_1980_; 
v_val_1979_ = lean_ctor_get(v_a_1978_, 0);
lean_inc_ref(v_val_1979_);
lean_dec_ref_known(v_a_1978_, 1);
v_isRec_1980_ = lean_ctor_get_uint8(v_val_1979_, sizeof(void*)*6);
if (v_isRec_1980_ == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref(v_val_1979_);
lean_dec(v_indName_1805_);
v___x_1981_ = lean_box(0);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v___x_1981_;
goto v___jp_1931_;
}
else
{
lean_object* v_toConstantVal_1982_; lean_object* v_numParams_1983_; lean_object* v_all_1984_; lean_object* v_numNested_1985_; lean_object* v_type_1986_; lean_object* v___x_1987_; 
v_toConstantVal_1982_ = lean_ctor_get(v_val_1979_, 0);
lean_inc_ref(v_toConstantVal_1982_);
v_numParams_1983_ = lean_ctor_get(v_val_1979_, 1);
lean_inc(v_numParams_1983_);
v_all_1984_ = lean_ctor_get(v_val_1979_, 3);
lean_inc(v_all_1984_);
v_numNested_1985_ = lean_ctor_get(v_val_1979_, 5);
lean_inc(v_numNested_1985_);
lean_dec_ref(v_val_1979_);
v_type_1986_ = lean_ctor_get(v_toConstantVal_1982_, 2);
lean_inc_ref(v_type_1986_);
lean_dec_ref(v_toConstantVal_1982_);
v___x_1987_ = l_Lean_Meta_isPropFormerType(v_type_1986_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; uint8_t v___x_1989_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = lean_unbox(v_a_1988_);
lean_dec(v_a_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
lean_inc_n(v_indName_1805_, 2);
v___x_1990_ = l_Lean_mkRecName(v_indName_1805_);
v___x_1991_ = l_Lean_mkBelowName(v_indName_1805_);
lean_inc(v___x_1991_);
lean_inc(v_numParams_1983_);
lean_inc(v___x_1990_);
v___x_1992_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1990_, v_numParams_1983_, v___x_1991_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_dec_ref_known(v___x_1992_, 1);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_List_get_x21Internal___redArg(v___x_1815_, v_all_1984_, v___x_1993_);
lean_dec(v_all_1984_);
v___x_1995_ = lean_name_eq(v___x_1994_, v_indName_1805_);
lean_dec(v_indName_1805_);
lean_dec(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
lean_dec(v_numNested_1985_);
lean_dec(v_numParams_1983_);
v___x_1996_ = lean_box(0);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v___x_1996_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1985_, v___x_1990_, v___x_1991_, v_numParams_1983_, v___x_1993_, v___x_1997_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_numNested_1985_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref_known(v___x_1998_, 1);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v___x_1997_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1937_ = v_a_1943_;
v___y_1938_ = v___x_1976_;
v_a_1939_ = v_a_1999_;
goto v___jp_1936_;
}
}
}
else
{
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1805_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v_a_2000_;
goto v___jp_1931_;
}
else
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1937_ = v_a_1943_;
v___y_1938_ = v___x_1976_;
v_a_1939_ = v_a_2001_;
goto v___jp_1936_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1805_);
v___x_2002_ = lean_box(0);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v___x_2002_;
goto v___jp_1931_;
}
}
else
{
lean_object* v_a_2003_; 
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1805_);
v_a_2003_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1987_, 1);
v___y_1937_ = v_a_1943_;
v___y_1938_ = v___x_1976_;
v_a_1939_ = v_a_2003_;
goto v___jp_1936_;
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_a_1978_);
lean_dec(v_indName_1805_);
v___x_2004_ = lean_box(0);
v___y_1932_ = v_a_1943_;
v___y_1933_ = v___x_1976_;
v_a_1934_ = v___x_2004_;
goto v___jp_1931_;
}
}
else
{
lean_object* v_a_2005_; 
lean_dec(v_indName_1805_);
v_a_2005_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1977_, 1);
v___y_1937_ = v_a_1943_;
v___y_1938_ = v___x_1976_;
v_a_1939_ = v_a_2005_;
goto v___jp_1936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_mkBelow(v_indName_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v___x_2091_, lean_object* v_inst_2092_, lean_object* v_R_2093_, lean_object* v_a_2094_, lean_object* v_b_2095_, lean_object* v_c_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2088_, v___x_2089_, v___x_2090_, v___x_2091_, v_a_2094_, v_b_2095_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v_inst_2107_, lean_object* v_R_2108_, lean_object* v_a_2109_, lean_object* v_b_2110_, lean_object* v_c_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2103_, v___x_2104_, v___x_2105_, v___x_2106_, v_inst_2107_, v_R_2108_, v_a_2109_, v_b_2110_, v_c_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v_upperBound_2103_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2118_, lean_object* v_x_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2119_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_x_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2126_, v_x_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
if (lean_obj_tag(v_a_2134_) == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = l_List_reverse___redArg(v_a_2135_);
return v___x_2136_;
}
else
{
lean_object* v_head_2137_; lean_object* v_tail_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2147_; 
v_head_2137_ = lean_ctor_get(v_a_2134_, 0);
v_tail_2138_ = lean_ctor_get(v_a_2134_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2140_ = v_a_2134_;
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_tail_2138_);
lean_inc(v_head_2137_);
lean_dec(v_a_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_MessageData_ofExpr(v_head_2137_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v_a_2135_);
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_a_2135_);
v___x_2144_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_a_2134_ = v_tail_2138_;
v_a_2135_ = v___x_2144_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2148_, lean_object* v_v_2149_, lean_object* v_i_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = lean_array_get_size(v_xs_2148_);
v___x_2152_ = lean_nat_dec_lt(v_i_2150_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_i_2150_);
v___x_2153_ = lean_box(0);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_array_fget_borrowed(v_xs_2148_, v_i_2150_);
v___x_2155_ = lean_expr_eqv(v___x_2154_, v_v_2149_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = lean_nat_add(v_i_2150_, v___x_2156_);
lean_dec(v_i_2150_);
v_i_2150_ = v___x_2157_;
goto _start;
}
else
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_i_2150_);
return v___x_2159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2160_, lean_object* v_v_2161_, lean_object* v_i_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2160_, v_v_2161_, v_i_2162_);
lean_dec_ref(v_v_2161_);
lean_dec_ref(v_xs_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2164_, lean_object* v_v_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2164_, v_v_2165_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2168_, lean_object* v_v_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2168_, v_v_2169_);
lean_dec_ref(v_v_2169_);
lean_dec_ref(v_xs_2168_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2171_, lean_object* v_v_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2171_, v_v_2172_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
else
{
lean_object* v_val_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
v_val_2175_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2173_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_val_2175_);
lean_dec(v___x_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_val_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2183_, lean_object* v_v_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2183_, v_v_2184_);
lean_dec_ref(v_v_2184_);
lean_dec_ref(v_xs_2183_);
return v_res_2185_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2191_ = l_Lean_stringToMessageData(v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2192_, lean_object* v_prods_2193_, lean_object* v_motives_2194_, lean_object* v_fs_2195_, lean_object* v_minor__type_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v_x_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 5)
{
lean_object* v_fn_2205_; lean_object* v_arg_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v_fn_2205_ = lean_ctor_get(v_x_2197_, 0);
lean_inc_ref(v_fn_2205_);
v_arg_2206_ = lean_ctor_get(v_x_2197_, 1);
lean_inc_ref(v_arg_2206_);
lean_dec_ref_known(v_x_2197_, 2);
v___x_2207_ = lean_array_set(v_x_2198_, v_x_2199_, v_arg_2206_);
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_sub(v_x_2199_, v___x_2208_);
lean_dec(v_x_2199_);
v_x_2197_ = v_fn_2205_;
v_x_2198_ = v___x_2207_;
v_x_2199_ = v___x_2209_;
goto _start;
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
lean_dec(v_x_2199_);
v___x_2211_ = l_Lean_instInhabitedExpr;
v___x_2212_ = l_Lean_Meta_PProdN_mk(v_rlvl_2192_, v_prods_2193_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v___x_2214_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2194_, v_x_2197_);
lean_dec_ref(v_x_2197_);
if (lean_obj_tag(v___x_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v_minor__type_2196_);
lean_dec_ref(v_motives_2194_);
v_val_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = lean_array_get_borrowed(v___x_2211_, v_fs_2195_, v_val_2215_);
lean_dec(v_val_2215_);
lean_inc(v_a_2213_);
v___x_2217_ = lean_array_push(v_x_2198_, v_a_2213_);
lean_inc(v___x_2216_);
v___x_2218_ = l_Lean_mkAppN(v___x_2216_, v___x_2217_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = l_Lean_Meta_mkPProdMk(v___x_2218_, v_a_2213_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v___x_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_x_2198_);
v___x_2220_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2221_ = l_Lean_MessageData_ofExpr(v_minor__type_2196_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2220_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2222_);
lean_ctor_set(v___x_2224_, 1, v___x_2223_);
v___x_2225_ = lean_array_to_list(v_motives_2194_);
v___x_2226_ = lean_box(0);
v___x_2227_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2225_, v___x_2226_);
v___x_2228_ = l_Lean_MessageData_ofList(v___x_2227_);
v___x_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2224_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2229_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2230_;
}
}
else
{
lean_dec_ref(v_x_2198_);
lean_dec_ref(v_x_2197_);
lean_dec_ref(v_minor__type_2196_);
lean_dec_ref(v_motives_2194_);
return v___x_2212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2231_, lean_object* v_prods_2232_, lean_object* v_motives_2233_, lean_object* v_fs_2234_, lean_object* v_minor__type_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2231_, v_prods_2232_, v_motives_2233_, v_fs_2234_, v_minor__type_2235_, v_x_2236_, v_x_2237_, v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_fs_2234_);
return v_res_2244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2245_; lean_object* v_dummy_2246_; 
v___x_2245_ = lean_box(0);
v_dummy_2246_ = l_Lean_Expr_sort___override(v___x_2245_);
return v_dummy_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2247_, lean_object* v_head_2248_, lean_object* v_belows_2249_, lean_object* v_prods_2250_, lean_object* v_rlvl_2251_, lean_object* v_fs_2252_, lean_object* v_minor__type_2253_, lean_object* v_tail_2254_, lean_object* v_arg__args_2255_, lean_object* v_arg__type_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2247_, v_head_2248_, v_belows_2249_, v_prods_2250_, v_rlvl_2251_, v_fs_2252_, v_minor__type_2253_, v_tail_2254_, v_arg__args_2255_, v_arg__type_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v_arg__args_2255_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2263_, lean_object* v_motives_2264_, lean_object* v_belows_2265_, lean_object* v_fs_2266_, lean_object* v_minor__type_2267_, lean_object* v_prods_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_){
_start:
{
if (lean_obj_tag(v_a_2269_) == 0)
{
lean_object* v_dummy_2275_; lean_object* v_nargs_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_dec_ref(v_belows_2265_);
v_dummy_2275_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2276_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2267_);
lean_inc(v_nargs_2276_);
v___x_2277_ = lean_mk_array(v_nargs_2276_, v_dummy_2275_);
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_nat_sub(v_nargs_2276_, v___x_2278_);
lean_dec(v_nargs_2276_);
lean_inc_ref(v_minor__type_2267_);
v___x_2280_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2263_, v_prods_2268_, v_motives_2264_, v_fs_2266_, v_minor__type_2267_, v_minor__type_2267_, v___x_2277_, v___x_2279_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
lean_dec_ref(v_fs_2266_);
return v___x_2280_;
}
else
{
lean_object* v_head_2281_; lean_object* v_tail_2282_; lean_object* v___f_2283_; lean_object* v___x_2284_; 
v_head_2281_ = lean_ctor_get(v_a_2269_, 0);
lean_inc_n(v_head_2281_, 2);
v_tail_2282_ = lean_ctor_get(v_a_2269_, 1);
lean_inc(v_tail_2282_);
lean_dec_ref_known(v_a_2269_, 2);
v___f_2283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2283_, 0, v_motives_2264_);
lean_closure_set(v___f_2283_, 1, v_head_2281_);
lean_closure_set(v___f_2283_, 2, v_belows_2265_);
lean_closure_set(v___f_2283_, 3, v_prods_2268_);
lean_closure_set(v___f_2283_, 4, v_rlvl_2263_);
lean_closure_set(v___f_2283_, 5, v_fs_2266_);
lean_closure_set(v___f_2283_, 6, v_minor__type_2267_);
lean_closure_set(v___f_2283_, 7, v_tail_2282_);
lean_inc(v_a_2273_);
lean_inc_ref(v_a_2272_);
lean_inc(v_a_2271_);
lean_inc_ref(v_a_2270_);
v___x_2284_ = lean_infer_type(v_head_2281_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref_known(v___x_2284_, 1);
v___x_2286_ = 0;
v___x_2287_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2285_, v___f_2283_, v___x_2286_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_);
return v___x_2287_;
}
else
{
lean_dec_ref(v___f_2283_);
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2288_, lean_object* v_rlvl_2289_, lean_object* v_motives_2290_, lean_object* v_belows_2291_, lean_object* v_fs_2292_, lean_object* v_minor__type_2293_, lean_object* v_tail_2294_, uint8_t v___x_2295_, uint8_t v___x_2296_, uint8_t v___x_2297_, lean_object* v_arg_x27_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_inc_ref(v_arg_x27_2298_);
v___x_2304_ = lean_array_push(v_prods_2288_, v_arg_x27_2298_);
v___x_2305_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2289_, v_motives_2290_, v_belows_2291_, v_fs_2292_, v_minor__type_2293_, v___x_2304_, v_tail_2294_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
v___x_2309_ = lean_array_push(v___x_2308_, v_arg_x27_2298_);
v___x_2310_ = l_Lean_Meta_mkLambdaFVars(v___x_2309_, v_a_2306_, v___x_2295_, v___x_2296_, v___x_2295_, v___x_2296_, v___x_2297_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec_ref(v___x_2309_);
return v___x_2310_;
}
else
{
lean_dec_ref(v_arg_x27_2298_);
return v___x_2305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2311_, lean_object* v_rlvl_2312_, lean_object* v_motives_2313_, lean_object* v_belows_2314_, lean_object* v_fs_2315_, lean_object* v_minor__type_2316_, lean_object* v_tail_2317_, lean_object* v___x_2318_, lean_object* v___x_2319_, lean_object* v___x_2320_, lean_object* v_arg_x27_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v___x_1689__boxed_2327_; uint8_t v___x_1690__boxed_2328_; uint8_t v___x_1691__boxed_2329_; lean_object* v_res_2330_; 
v___x_1689__boxed_2327_ = lean_unbox(v___x_2318_);
v___x_1690__boxed_2328_ = lean_unbox(v___x_2319_);
v___x_1691__boxed_2329_ = lean_unbox(v___x_2320_);
v_res_2330_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2311_, v_rlvl_2312_, v_motives_2313_, v_belows_2314_, v_fs_2315_, v_minor__type_2316_, v_tail_2317_, v___x_1689__boxed_2327_, v___x_1690__boxed_2328_, v___x_1691__boxed_2329_, v_arg_x27_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2331_, lean_object* v_head_2332_, lean_object* v_belows_2333_, lean_object* v_arg__type_2334_, lean_object* v_prods_2335_, lean_object* v_rlvl_2336_, lean_object* v_fs_2337_, lean_object* v_minor__type_2338_, lean_object* v_tail_2339_, lean_object* v_arg__args_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
if (lean_obj_tag(v_x_2341_) == 5)
{
lean_object* v_fn_2349_; lean_object* v_arg_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_fn_2349_ = lean_ctor_get(v_x_2341_, 0);
lean_inc_ref(v_fn_2349_);
v_arg_2350_ = lean_ctor_get(v_x_2341_, 1);
lean_inc_ref(v_arg_2350_);
lean_dec_ref_known(v_x_2341_, 2);
v___x_2351_ = lean_array_set(v_x_2342_, v_x_2343_, v_arg_2350_);
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_sub(v_x_2343_, v___x_2352_);
lean_dec(v_x_2343_);
v_x_2341_ = v_fn_2349_;
v_x_2342_ = v___x_2351_;
v_x_2343_ = v___x_2353_;
goto _start;
}
else
{
lean_object* v___x_2355_; 
lean_dec(v_x_2343_);
v___x_2355_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2331_, v_x_2341_);
lean_dec_ref(v_x_2341_);
if (lean_obj_tag(v___x_2355_) == 1)
{
lean_object* v_val_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_val_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_val_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = l_Lean_instInhabitedExpr;
v___x_2358_ = l_Lean_Expr_fvarId_x21(v_head_2332_);
lean_dec_ref(v_head_2332_);
v___x_2359_ = l_Lean_FVarId_getUserName___redArg(v___x_2358_, v___y_2344_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = lean_array_get_borrowed(v___x_2357_, v_belows_2333_, v_val_2356_);
lean_dec(v_val_2356_);
lean_inc(v___x_2361_);
v___x_2362_ = l_Lean_mkAppN(v___x_2361_, v_x_2342_);
lean_dec_ref(v_x_2342_);
v___x_2363_ = l_Lean_Meta_mkPProd(v_arg__type_2334_, v___x_2362_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; uint8_t v___x_2365_; uint8_t v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = 0;
v___x_2366_ = 1;
v___x_2367_ = 1;
v___x_2368_ = lean_box(v___x_2365_);
v___x_2369_ = lean_box(v___x_2366_);
v___x_2370_ = lean_box(v___x_2367_);
v___f_2371_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2371_, 0, v_prods_2335_);
lean_closure_set(v___f_2371_, 1, v_rlvl_2336_);
lean_closure_set(v___f_2371_, 2, v_motives_2331_);
lean_closure_set(v___f_2371_, 3, v_belows_2333_);
lean_closure_set(v___f_2371_, 4, v_fs_2337_);
lean_closure_set(v___f_2371_, 5, v_minor__type_2338_);
lean_closure_set(v___f_2371_, 6, v_tail_2339_);
lean_closure_set(v___f_2371_, 7, v___x_2368_);
lean_closure_set(v___f_2371_, 8, v___x_2369_);
lean_closure_set(v___f_2371_, 9, v___x_2370_);
v___x_2372_ = l_Lean_Meta_mkForallFVars(v_arg__args_2340_, v_a_2364_, v___x_2365_, v___x_2366_, v___x_2366_, v___x_2367_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2360_, v_a_2373_, v___f_2371_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v___x_2374_;
}
else
{
lean_dec_ref(v___f_2371_);
lean_dec(v_a_2360_);
return v___x_2372_;
}
}
else
{
lean_dec(v_a_2360_);
lean_dec(v_tail_2339_);
lean_dec_ref(v_minor__type_2338_);
lean_dec_ref(v_fs_2337_);
lean_dec(v_rlvl_2336_);
lean_dec_ref(v_prods_2335_);
lean_dec_ref(v_belows_2333_);
lean_dec_ref(v_motives_2331_);
return v___x_2363_;
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v_val_2356_);
lean_dec_ref(v_x_2342_);
lean_dec(v_tail_2339_);
lean_dec_ref(v_minor__type_2338_);
lean_dec_ref(v_fs_2337_);
lean_dec(v_rlvl_2336_);
lean_dec_ref(v_prods_2335_);
lean_dec_ref(v_arg__type_2334_);
lean_dec_ref(v_belows_2333_);
lean_dec_ref(v_motives_2331_);
v_a_2375_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2359_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2359_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v___x_2383_; 
lean_dec(v___x_2355_);
lean_dec_ref(v_x_2342_);
lean_dec_ref(v_arg__type_2334_);
v___x_2383_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2336_, v_motives_2331_, v_belows_2333_, v_fs_2337_, v_minor__type_2338_, v_prods_2335_, v_tail_2339_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; uint8_t v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = lean_unsigned_to_nat(1u);
v___x_2386_ = lean_mk_empty_array_with_capacity(v___x_2385_);
v___x_2387_ = lean_array_push(v___x_2386_, v_head_2332_);
v___x_2388_ = 0;
v___x_2389_ = 1;
v___x_2390_ = 1;
v___x_2391_ = l_Lean_Meta_mkLambdaFVars(v___x_2387_, v_a_2384_, v___x_2388_, v___x_2389_, v___x_2388_, v___x_2389_, v___x_2390_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec_ref(v___x_2387_);
return v___x_2391_;
}
else
{
lean_dec_ref(v_head_2332_);
return v___x_2383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2392_, lean_object* v_head_2393_, lean_object* v_belows_2394_, lean_object* v_prods_2395_, lean_object* v_rlvl_2396_, lean_object* v_fs_2397_, lean_object* v_minor__type_2398_, lean_object* v_tail_2399_, lean_object* v_arg__args_2400_, lean_object* v_arg__type_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_dummy_2407_; lean_object* v_nargs_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_dummy_2407_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2408_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2401_);
lean_inc(v_nargs_2408_);
v___x_2409_ = lean_mk_array(v_nargs_2408_, v_dummy_2407_);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_sub(v_nargs_2408_, v___x_2410_);
lean_dec(v_nargs_2408_);
lean_inc_ref(v_arg__type_2401_);
v___x_2412_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2392_, v_head_2393_, v_belows_2394_, v_arg__type_2401_, v_prods_2395_, v_rlvl_2396_, v_fs_2397_, v_minor__type_2398_, v_tail_2399_, v_arg__args_2400_, v_arg__type_2401_, v___x_2409_, v___x_2411_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2413_, lean_object* v_motives_2414_, lean_object* v_belows_2415_, lean_object* v_fs_2416_, lean_object* v_minor__type_2417_, lean_object* v_prods_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2413_, v_motives_2414_, v_belows_2415_, v_fs_2416_, v_minor__type_2417_, v_prods_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
lean_dec(v_a_2423_);
lean_dec_ref(v_a_2422_);
lean_dec(v_a_2421_);
lean_dec_ref(v_a_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2426_ = _args[0];
lean_object* v_head_2427_ = _args[1];
lean_object* v_belows_2428_ = _args[2];
lean_object* v_arg__type_2429_ = _args[3];
lean_object* v_prods_2430_ = _args[4];
lean_object* v_rlvl_2431_ = _args[5];
lean_object* v_fs_2432_ = _args[6];
lean_object* v_minor__type_2433_ = _args[7];
lean_object* v_tail_2434_ = _args[8];
lean_object* v_arg__args_2435_ = _args[9];
lean_object* v_x_2436_ = _args[10];
lean_object* v_x_2437_ = _args[11];
lean_object* v_x_2438_ = _args[12];
lean_object* v___y_2439_ = _args[13];
lean_object* v___y_2440_ = _args[14];
lean_object* v___y_2441_ = _args[15];
lean_object* v___y_2442_ = _args[16];
lean_object* v___y_2443_ = _args[17];
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2426_, v_head_2427_, v_belows_2428_, v_arg__type_2429_, v_prods_2430_, v_rlvl_2431_, v_fs_2432_, v_minor__type_2433_, v_tail_2434_, v_arg__args_2435_, v_x_2436_, v_x_2437_, v_x_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec_ref(v_arg__args_2435_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2445_, lean_object* v_motives_2446_, lean_object* v_belows_2447_, lean_object* v_fs_2448_, lean_object* v_minor__args_2449_, lean_object* v_minor__type_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2457_ = lean_array_to_list(v_minor__args_2449_);
v___x_2458_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2445_, v_motives_2446_, v_belows_2447_, v_fs_2448_, v_minor__type_2450_, v___x_2456_, v___x_2457_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2459_, lean_object* v_motives_2460_, lean_object* v_belows_2461_, lean_object* v_fs_2462_, lean_object* v_minor__args_2463_, lean_object* v_minor__type_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v_res_2470_; 
v_res_2470_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2459_, v_motives_2460_, v_belows_2461_, v_fs_2462_, v_minor__args_2463_, v_minor__type_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2471_, lean_object* v_motives_2472_, lean_object* v_belows_2473_, lean_object* v_fs_2474_, lean_object* v_minorType_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v___f_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; 
v___f_2481_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2481_, 0, v_rlvl_2471_);
lean_closure_set(v___f_2481_, 1, v_motives_2472_);
lean_closure_set(v___f_2481_, 2, v_belows_2473_);
lean_closure_set(v___f_2481_, 3, v_fs_2474_);
v___x_2482_ = 0;
v___x_2483_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2475_, v___f_2481_, v___x_2482_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2484_, lean_object* v_motives_2485_, lean_object* v_belows_2486_, lean_object* v_fs_2487_, lean_object* v_minorType_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2484_, v_motives_2485_, v_belows_2486_, v_fs_2487_, v_minorType_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
lean_dec(v_a_2492_);
lean_dec_ref(v_a_2491_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___f_2501_; lean_object* v___x_27356__overap_2502_; lean_object* v___x_2503_; 
v___f_2501_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27356__overap_2502_ = lean_panic_fn_borrowed(v___f_2501_, v_msg_2495_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
v___x_2503_ = lean_apply_5(v___x_27356__overap_2502_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, lean_box(0));
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = l_Lean_Expr_hasMVar(v_e_2511_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_e_2511_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v_mctx_2517_; lean_object* v___x_2518_; lean_object* v_fst_2519_; lean_object* v_snd_2520_; lean_object* v___x_2521_; lean_object* v_cache_2522_; lean_object* v_zetaDeltaFVarIds_2523_; lean_object* v_postponed_2524_; lean_object* v_diag_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2534_; 
v___x_2516_ = lean_st_ref_get(v___y_2512_);
v_mctx_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_ref(v_mctx_2517_);
lean_dec(v___x_2516_);
v___x_2518_ = l_Lean_instantiateMVarsCore(v_mctx_2517_, v_e_2511_);
v_fst_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_fst_2519_);
v_snd_2520_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2520_);
lean_dec_ref(v___x_2518_);
v___x_2521_ = lean_st_ref_take(v___y_2512_);
v_cache_2522_ = lean_ctor_get(v___x_2521_, 1);
v_zetaDeltaFVarIds_2523_ = lean_ctor_get(v___x_2521_, 2);
v_postponed_2524_ = lean_ctor_get(v___x_2521_, 3);
v_diag_2525_ = lean_ctor_get(v___x_2521_, 4);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2521_, 0);
lean_dec(v_unused_2535_);
v___x_2527_ = v___x_2521_;
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_diag_2525_);
lean_inc(v_postponed_2524_);
lean_inc(v_zetaDeltaFVarIds_2523_);
lean_inc(v_cache_2522_);
lean_dec(v___x_2521_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2534_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_snd_2520_);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_snd_2520_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_cache_2522_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_zetaDeltaFVarIds_2523_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_postponed_2524_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_diag_2525_);
v___x_2530_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_st_ref_put(v___y_2512_, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_fst_2519_);
return v___x_2532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2536_, v___y_2537_);
lean_dec(v___y_2537_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; 
v___x_2546_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2540_, v___y_2542_);
return v___x_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v_env_2558_; lean_object* v_toConstantVal_2559_; lean_object* v_value_2560_; lean_object* v_all_2561_; uint8_t v___y_2563_; lean_object* v_type_2571_; uint8_t v___x_2572_; 
v___x_2557_ = lean_st_ref_get(v___y_2555_);
v_env_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc_ref_n(v_env_2558_, 2);
lean_dec(v___x_2557_);
v_toConstantVal_2559_ = lean_ctor_get(v_thm_2554_, 0);
v_value_2560_ = lean_ctor_get(v_thm_2554_, 1);
v_all_2561_ = lean_ctor_get(v_thm_2554_, 2);
v_type_2571_ = lean_ctor_get(v_toConstantVal_2559_, 2);
v___x_2572_ = l_Lean_Environment_hasUnsafe(v_env_2558_, v_type_2571_);
if (v___x_2572_ == 0)
{
uint8_t v___x_2573_; 
v___x_2573_ = l_Lean_Environment_hasUnsafe(v_env_2558_, v_value_2560_);
v___y_2563_ = v___x_2573_;
goto v___jp_2562_;
}
else
{
lean_dec_ref(v_env_2558_);
v___y_2563_ = v___x_2572_;
goto v___jp_2562_;
}
v___jp_2562_:
{
if (v___y_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_thm_2554_);
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_inc(v_all_2561_);
lean_inc_ref(v_value_2560_);
lean_inc_ref(v_toConstantVal_2559_);
lean_dec_ref(v_thm_2554_);
v___x_2566_ = lean_box(0);
v___x_2567_ = 0;
v___x_2568_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2568_, 0, v_toConstantVal_2559_);
lean_ctor_set(v___x_2568_, 1, v_value_2560_);
lean_ctor_set(v___x_2568_, 2, v___x_2566_);
lean_ctor_set(v___x_2568_, 3, v_all_2561_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*4, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
return v___x_2570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2574_, v___y_2575_);
lean_dec(v___y_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2578_, v___y_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2593_, lean_object* v___x_2594_, lean_object* v___x_2595_, lean_object* v_all_2596_, lean_object* v___x_2597_, lean_object* v___x_2598_, lean_object* v___x_2599_, lean_object* v_x_2600_){
_start:
{
lean_object* v___y_2602_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = lean_array_get_size(v_all_2596_);
v___x_2607_ = lean_nat_dec_lt(v_x_2600_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2608_ = lean_array_get_borrowed(v___x_2597_, v_all_2596_, v___x_2598_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2610_ = lean_nat_sub(v_x_2600_, v___x_2606_);
v___x_2611_ = lean_nat_add(v___x_2610_, v___x_2599_);
lean_dec(v___x_2610_);
v___x_2612_ = l_Nat_reprFast(v___x_2611_);
v___x_2613_ = lean_string_append(v___x_2609_, v___x_2612_);
lean_dec_ref(v___x_2612_);
lean_inc(v___x_2608_);
v___x_2614_ = l_Lean_Name_str___override(v___x_2608_, v___x_2613_);
v___y_2602_ = v___x_2614_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_array_fget_borrowed(v_all_2596_, v_x_2600_);
lean_inc(v___x_2615_);
v___x_2616_ = l_Lean_mkBelowName(v___x_2615_);
v___y_2602_ = v___x_2616_;
goto v___jp_2601_;
}
v___jp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2603_ = l_Lean_Expr_const___override(v___y_2602_, v___x_2593_);
v___x_2604_ = l_Array_append___redArg(v___x_2594_, v___x_2595_);
v___x_2605_ = l_Lean_mkAppN(v___x_2603_, v___x_2604_);
lean_dec_ref(v___x_2604_);
return v___x_2605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v_all_2620_, lean_object* v___x_2621_, lean_object* v___x_2622_, lean_object* v___x_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2617_, v___x_2618_, v___x_2619_, v_all_2620_, v___x_2621_, v___x_2622_, v___x_2623_, v_x_2624_);
lean_dec(v_x_2624_);
lean_dec(v___x_2623_);
lean_dec(v___x_2622_);
lean_dec(v___x_2621_);
lean_dec_ref(v_all_2620_);
lean_dec_ref(v___x_2619_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v_fs_2629_, lean_object* v_as_2630_, size_t v_sz_2631_, size_t v_i_2632_, lean_object* v_b_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_lt(v_i_2632_, v_sz_2631_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
lean_dec_ref(v_fs_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___x_2627_);
lean_dec(v___x_2626_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_b_2633_);
return v___x_2640_;
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2642_; 
v_a_2641_ = lean_array_uget_borrowed(v_as_2630_, v_i_2632_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc(v_a_2641_);
v___x_2642_ = lean_infer_type(v_a_2641_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
lean_inc_ref(v_fs_2629_);
lean_inc_ref(v___x_2628_);
lean_inc_ref(v___x_2627_);
lean_inc(v___x_2626_);
v___x_2644_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2626_, v___x_2627_, v___x_2628_, v_fs_2629_, v_a_2643_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; size_t v___x_2647_; size_t v___x_2648_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = l_Lean_Expr_app___override(v_b_2633_, v_a_2645_);
v___x_2647_ = ((size_t)1ULL);
v___x_2648_ = lean_usize_add(v_i_2632_, v___x_2647_);
v_i_2632_ = v___x_2648_;
v_b_2633_ = v___x_2646_;
goto _start;
}
else
{
lean_dec_ref(v_b_2633_);
lean_dec_ref(v_fs_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___x_2627_);
lean_dec(v___x_2626_);
return v___x_2644_;
}
}
else
{
lean_dec_ref(v_b_2633_);
lean_dec_ref(v_fs_2629_);
lean_dec_ref(v___x_2628_);
lean_dec_ref(v___x_2627_);
lean_dec(v___x_2626_);
return v___x_2642_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2650_, lean_object* v___x_2651_, lean_object* v___x_2652_, lean_object* v_fs_2653_, lean_object* v_as_2654_, lean_object* v_sz_2655_, lean_object* v_i_2656_, lean_object* v_b_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
size_t v_sz_boxed_2663_; size_t v_i_boxed_2664_; lean_object* v_res_2665_; 
v_sz_boxed_2663_ = lean_unbox_usize(v_sz_2655_);
lean_dec(v_sz_2655_);
v_i_boxed_2664_ = lean_unbox_usize(v_i_2656_);
lean_dec(v_i_2656_);
v_res_2665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2650_, v___x_2651_, v___x_2652_, v_fs_2653_, v_as_2654_, v_sz_boxed_2663_, v_i_boxed_2664_, v_b_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_as_2654_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2666_, lean_object* v___x_2667_, uint8_t v___x_2668_, lean_object* v_targs_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = l_Lean_mkAppN(v_a_2666_, v_targs_2669_);
v___x_2677_ = l_Lean_mkAppN(v___x_2667_, v_targs_2669_);
v___x_2678_ = l_Lean_Meta_mkPProd(v___x_2676_, v___x_2677_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; uint8_t v___x_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = 0;
v___x_2681_ = 1;
v___x_2682_ = l_Lean_Meta_mkLambdaFVars(v_targs_2669_, v_a_2679_, v___x_2680_, v___x_2668_, v___x_2680_, v___x_2668_, v___x_2681_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2682_;
}
else
{
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2683_, lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v_targs_2686_, lean_object* v_x_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
uint8_t v___x_30628__boxed_2693_; lean_object* v_res_2694_; 
v___x_30628__boxed_2693_ = lean_unbox(v___x_2685_);
v_res_2694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2683_, v___x_2684_, v___x_30628__boxed_2693_, v_targs_2686_, v_x_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec_ref(v_x_2687_);
lean_dec_ref(v_targs_2686_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_as_2697_, size_t v_sz_2698_, size_t v_i_2699_, lean_object* v_b_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
uint8_t v___x_2706_; 
v___x_2706_ = lean_usize_dec_lt(v_i_2699_, v_sz_2698_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_b_2700_);
return v___x_2707_;
}
else
{
lean_object* v_snd_2708_; lean_object* v_fst_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2766_; 
v_snd_2708_ = lean_ctor_get(v_b_2700_, 1);
v_fst_2709_ = lean_ctor_get(v_b_2700_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_b_2700_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2711_ = v_b_2700_;
v_isShared_2712_ = v_isSharedCheck_2766_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2708_);
lean_inc(v_fst_2709_);
lean_dec(v_b_2700_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2766_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_array_2713_; lean_object* v_start_2714_; lean_object* v_stop_2715_; uint8_t v___x_2716_; 
v_array_2713_ = lean_ctor_get(v_snd_2708_, 0);
v_start_2714_ = lean_ctor_get(v_snd_2708_, 1);
v_stop_2715_ = lean_ctor_get(v_snd_2708_, 2);
v___x_2716_ = lean_nat_dec_lt(v_start_2714_, v_stop_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2718_; 
if (v_isShared_2712_ == 0)
{
v___x_2718_ = v___x_2711_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_fst_2709_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v_snd_2708_);
v___x_2718_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
return v___x_2719_;
}
}
else
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2762_; 
lean_inc(v_stop_2715_);
lean_inc(v_start_2714_);
lean_inc_ref(v_array_2713_);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_snd_2708_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; lean_object* v_unused_2764_; lean_object* v_unused_2765_; 
v_unused_2763_ = lean_ctor_get(v_snd_2708_, 2);
lean_dec(v_unused_2763_);
v_unused_2764_ = lean_ctor_get(v_snd_2708_, 1);
lean_dec(v_unused_2764_);
v_unused_2765_ = lean_ctor_get(v_snd_2708_, 0);
lean_dec(v_unused_2765_);
v___x_2722_ = v_snd_2708_;
v_isShared_2723_ = v_isSharedCheck_2762_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v_snd_2708_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2762_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
uint8_t v___x_2724_; lean_object* v_a_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2724_ = lean_nat_dec_lt(v___x_2695_, v___x_2696_);
v_a_2725_ = lean_array_uget_borrowed(v_as_2697_, v_i_2699_);
v___x_2726_ = lean_array_fget_borrowed(v_array_2713_, v_start_2714_);
v___x_2727_ = lean_box(v___x_2724_);
lean_inc(v___x_2726_);
lean_inc(v_a_2725_);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2728_, 0, v_a_2725_);
lean_closure_set(v___f_2728_, 1, v___x_2726_);
lean_closure_set(v___f_2728_, 2, v___x_2727_);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_nat_add(v_start_2714_, v___x_2729_);
lean_dec(v_start_2714_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2730_);
v___x_2732_ = v___x_2722_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_array_2713_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v___x_2730_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_stop_2715_);
v___x_2732_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
lean_inc(v___y_2704_);
lean_inc_ref(v___y_2703_);
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v_a_2725_);
v___x_2733_ = lean_infer_type(v_a_2725_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
v___x_2735_ = 0;
v___x_2736_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2734_, v___f_2728_, v___x_2735_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = l_Lean_Expr_app___override(v_fst_2709_, v_a_2737_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2732_);
lean_ctor_set(v___x_2711_, 0, v___x_2738_);
v___x_2740_ = v___x_2711_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2732_);
v___x_2740_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
size_t v___x_2741_; size_t v___x_2742_; 
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2699_, v___x_2741_);
v_i_2699_ = v___x_2742_;
v_b_2700_ = v___x_2740_;
goto _start;
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___x_2732_);
lean_del_object(v___x_2711_);
lean_dec(v_fst_2709_);
v_a_2745_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2736_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2736_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec_ref(v___x_2732_);
lean_dec_ref(v___f_2728_);
lean_del_object(v___x_2711_);
lean_dec(v_fst_2709_);
v_a_2753_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2733_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2733_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2767_, lean_object* v___x_2768_, lean_object* v_as_2769_, lean_object* v_sz_2770_, lean_object* v_i_2771_, lean_object* v_b_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
size_t v_sz_boxed_2778_; size_t v_i_boxed_2779_; lean_object* v_res_2780_; 
v_sz_boxed_2778_ = lean_unbox_usize(v_sz_2770_);
lean_dec(v_sz_2770_);
v_i_boxed_2779_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_res_2780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2767_, v___x_2768_, v_as_2769_, v_sz_boxed_2778_, v_i_boxed_2779_, v_b_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec_ref(v_as_2769_);
lean_dec(v___x_2768_);
lean_dec(v___x_2767_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2781_, size_t v_sz_2782_, size_t v_i_2783_, lean_object* v_b_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_usize_dec_lt(v_i_2783_, v_sz_2782_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_b_2784_);
return v___x_2791_;
}
else
{
lean_object* v_a_2792_; lean_object* v_toInductionSubgoal_2793_; lean_object* v_mvarId_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2792_ = lean_array_uget_borrowed(v_as_2781_, v_i_2783_);
v_toInductionSubgoal_2793_ = lean_ctor_get(v_a_2792_, 0);
v_mvarId_2794_ = lean_ctor_get(v_toInductionSubgoal_2793_, 0);
v___x_2795_ = 0;
v___x_2796_ = lean_box(0);
lean_inc(v_mvarId_2794_);
v___x_2797_ = l_Lean_MVarId_refl(v_mvarId_2794_, v___x_2795_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2797_) == 0)
{
size_t v___x_2798_; size_t v___x_2799_; 
lean_dec_ref_known(v___x_2797_, 1);
v___x_2798_ = ((size_t)1ULL);
v___x_2799_ = lean_usize_add(v_i_2783_, v___x_2798_);
v_i_2783_ = v___x_2799_;
v_b_2784_ = v___x_2796_;
goto _start;
}
else
{
return v___x_2797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2801_, lean_object* v_sz_2802_, lean_object* v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
size_t v_sz_boxed_2810_; size_t v_i_boxed_2811_; lean_object* v_res_2812_; 
v_sz_boxed_2810_ = lean_unbox_usize(v_sz_2802_);
lean_dec(v_sz_2802_);
v_i_boxed_2811_ = lean_unbox_usize(v_i_2803_);
lean_dec(v_i_2803_);
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2801_, v_sz_boxed_2810_, v_i_boxed_2811_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v_as_2801_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2813_, lean_object* v_tail_2814_, lean_object* v_recName_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_val_2827_, uint8_t v___x_2828_, lean_object* v_brecOnGoName_2829_, lean_object* v_levelParams_2830_, lean_object* v___x_2831_, lean_object* v_brecOnName_2832_, lean_object* v___x_2833_, lean_object* v_brecOnEqName_2834_, lean_object* v_fs_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; size_t v_sz_2845_; size_t v___x_2846_; lean_object* v___x_2847_; 
lean_inc(v___x_2813_);
v___x_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2813_);
lean_ctor_set(v___x_2841_, 1, v_tail_2814_);
v___x_2842_ = l_Lean_Expr_const___override(v_recName_2815_, v___x_2841_);
v___x_2843_ = l_Lean_mkAppN(v___x_2842_, v___x_2816_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2817_);
v_sz_2845_ = lean_array_size(v___x_2818_);
v___x_2846_ = ((size_t)0ULL);
v___x_2847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2819_, v___x_2820_, v___x_2818_, v_sz_2845_, v___x_2846_, v___x_2844_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v_fst_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_3214_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v_fst_2849_ = lean_ctor_get(v_a_2848_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_a_2848_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v_a_2848_, 1);
lean_dec(v_unused_3215_);
v___x_2851_ = v_a_2848_;
v_isShared_2852_ = v_isSharedCheck_3214_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_fst_2849_);
lean_dec(v_a_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_3214_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
size_t v_sz_2853_; lean_object* v___x_2854_; 
v_sz_2853_ = lean_array_size(v___x_2821_);
lean_inc_ref(v_fs_2835_);
lean_inc_ref(v___x_2822_);
lean_inc_ref(v___x_2818_);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2813_, v___x_2818_, v___x_2822_, v_fs_2835_, v___x_2821_, v_sz_2853_, v___x_2846_, v_fst_2849_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = l_Lean_mkAppN(v_a_2855_, v___x_2823_);
lean_inc_ref_n(v___x_2824_, 3);
v___x_2857_ = l_Lean_Expr_app___override(v___x_2856_, v___x_2824_);
v___x_2858_ = l_Array_append___redArg(v___x_2816_, v___x_2818_);
v___x_2859_ = l_Array_append___redArg(v___x_2858_, v___x_2823_);
v___x_2860_ = lean_mk_empty_array_with_capacity(v___x_2825_);
v___x_2861_ = lean_array_push(v___x_2860_, v___x_2824_);
v___x_2862_ = l_Array_append___redArg(v___x_2859_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = l_Array_append___redArg(v___x_2862_, v_fs_2835_);
v___x_2864_ = lean_array_get(v___x_2826_, v___x_2818_, v_val_2827_);
lean_dec_ref(v___x_2818_);
v___x_2865_ = lean_array_push(v___x_2823_, v___x_2824_);
v___x_2866_ = l_Lean_mkAppN(v___x_2864_, v___x_2865_);
v___x_2867_ = lean_array_get(v___x_2826_, v___x_2822_, v_val_2827_);
lean_dec_ref(v___x_2822_);
v___x_2868_ = l_Lean_mkAppN(v___x_2867_, v___x_2865_);
lean_inc_ref(v___x_2866_);
v___x_2869_ = l_Lean_Meta_mkPProd(v___x_2866_, v___x_2868_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; uint8_t v___x_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = 0;
v___x_2872_ = 1;
v___x_2873_ = l_Lean_Meta_mkForallFVars(v___x_2863_, v_a_2870_, v___x_2871_, v___x_2828_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_Meta_mkLambdaFVars(v___x_2863_, v___x_2857_, v___x_2871_, v___x_2828_, v___x_2871_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_3181_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = lean_box(1);
lean_inc(v_levelParams_2830_);
lean_inc(v_brecOnGoName_2829_);
v___x_2878_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2829_, v_levelParams_2830_, v_a_2874_, v_a_2876_, v___x_2877_, v___y_2839_);
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_3181_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_3181_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
lean_inc(v_a_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 1);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_3180_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_addDecl(v___x_2884_, v___x_2871_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_toConstantVal_2886_; lean_object* v_name_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref_known(v___x_2885_, 1);
v_toConstantVal_2886_ = lean_ctor_get(v_a_2879_, 0);
lean_inc_ref(v_toConstantVal_2886_);
lean_dec(v_a_2879_);
v_name_2887_ = lean_ctor_get(v_toConstantVal_2886_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v_toConstantVal_2886_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; lean_object* v_unused_3179_; 
v_unused_3178_ = lean_ctor_get(v_toConstantVal_2886_, 2);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_toConstantVal_2886_, 1);
lean_dec(v_unused_3179_);
v___x_2889_ = v_toConstantVal_2886_;
v_isShared_2890_ = v_isSharedCheck_3177_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_name_2887_);
lean_dec(v_toConstantVal_2886_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_3177_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v_env_2893_; lean_object* v_nextMacroScope_2894_; lean_object* v_ngen_2895_; lean_object* v_auxDeclNGen_2896_; lean_object* v_traceState_2897_; lean_object* v_recordedDeps_2898_; lean_object* v_messages_2899_; lean_object* v_infoState_2900_; lean_object* v_snapshotTasks_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_3175_; 
lean_inc(v_name_2887_);
v___x_2891_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2887_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2891_);
v___x_2892_ = lean_st_ref_take(v___y_2839_);
v_env_2893_ = lean_ctor_get(v___x_2892_, 0);
v_nextMacroScope_2894_ = lean_ctor_get(v___x_2892_, 1);
v_ngen_2895_ = lean_ctor_get(v___x_2892_, 2);
v_auxDeclNGen_2896_ = lean_ctor_get(v___x_2892_, 3);
v_traceState_2897_ = lean_ctor_get(v___x_2892_, 4);
v_recordedDeps_2898_ = lean_ctor_get(v___x_2892_, 6);
v_messages_2899_ = lean_ctor_get(v___x_2892_, 7);
v_infoState_2900_ = lean_ctor_get(v___x_2892_, 8);
v_snapshotTasks_2901_ = lean_ctor_get(v___x_2892_, 9);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_2892_, 5);
lean_dec(v_unused_3176_);
v___x_2903_ = v___x_2892_;
v_isShared_2904_ = v_isSharedCheck_3175_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_snapshotTasks_2901_);
lean_inc(v_infoState_2900_);
lean_inc(v_messages_2899_);
lean_inc(v_recordedDeps_2898_);
lean_inc(v_traceState_2897_);
lean_inc(v_auxDeclNGen_2896_);
lean_inc(v_ngen_2895_);
lean_inc(v_nextMacroScope_2894_);
lean_inc(v_env_2893_);
lean_dec(v___x_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_3175_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2905_ = l_Lean_addProtected(v_env_2893_, v_name_2887_);
v___x_2906_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 5, v___x_2906_);
lean_ctor_set(v___x_2903_, 0, v___x_2905_);
v___x_2908_ = v___x_2903_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_nextMacroScope_2894_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_ngen_2895_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_auxDeclNGen_2896_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_traceState_2897_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3174_, 6, v_recordedDeps_2898_);
lean_ctor_set(v_reuseFailAlloc_3174_, 7, v_messages_2899_);
lean_ctor_set(v_reuseFailAlloc_3174_, 8, v_infoState_2900_);
lean_ctor_set(v_reuseFailAlloc_3174_, 9, v_snapshotTasks_2901_);
v___x_2908_ = v_reuseFailAlloc_3174_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_mctx_2911_; lean_object* v_zetaDeltaFVarIds_2912_; lean_object* v_postponed_2913_; lean_object* v_diag_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_3172_; 
v___x_2909_ = lean_st_ref_put(v___y_2839_, v___x_2908_);
v___x_2910_ = lean_st_ref_take(v___y_2837_);
v_mctx_2911_ = lean_ctor_get(v___x_2910_, 0);
v_zetaDeltaFVarIds_2912_ = lean_ctor_get(v___x_2910_, 2);
v_postponed_2913_ = lean_ctor_get(v___x_2910_, 3);
v_diag_2914_ = lean_ctor_get(v___x_2910_, 4);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_2910_, 1);
lean_dec(v_unused_3173_);
v___x_2916_ = v___x_2910_;
v_isShared_2917_ = v_isSharedCheck_3172_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_diag_2914_);
lean_inc(v_postponed_2913_);
lean_inc(v_zetaDeltaFVarIds_2912_);
lean_inc(v_mctx_2911_);
lean_dec(v___x_2910_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_3172_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2918_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2918_);
v___x_2920_ = v___x_2916_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_mctx_2911_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3171_, 2, v_zetaDeltaFVarIds_2912_);
lean_ctor_set(v_reuseFailAlloc_3171_, 3, v_postponed_2913_);
lean_ctor_set(v_reuseFailAlloc_3171_, 4, v_diag_2914_);
v___x_2920_ = v_reuseFailAlloc_3171_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2921_ = lean_st_ref_put(v___y_2837_, v___x_2920_);
lean_inc(v___x_2831_);
v___x_2922_ = l_Lean_Expr_const___override(v_brecOnGoName_2829_, v___x_2831_);
v___x_2923_ = l_Lean_mkAppN(v___x_2922_, v___x_2863_);
lean_inc_ref(v___x_2923_);
v___x_2924_ = l_Lean_Meta_mkPProdFstM(v___x_2923_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_mkLambdaFVars(v___x_2863_, v_a_2925_, v___x_2871_, v___x_2828_, v___x_2871_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = l_Lean_Meta_mkForallFVars(v___x_2863_, v___x_2866_, v___x_2871_, v___x_2828_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3146_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
lean_inc(v_levelParams_2830_);
v___x_2930_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2832_, v_levelParams_2830_, v_a_2929_, v_a_2927_, v___x_2877_, v___y_2839_);
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_3146_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3146_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
lean_inc(v_a_2931_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 1);
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_3145_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_Lean_addDecl(v___x_2936_, v___x_2871_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_toConstantVal_2938_; lean_object* v_name_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref_known(v___x_2937_, 1);
v_toConstantVal_2938_ = lean_ctor_get(v_a_2931_, 0);
lean_inc_ref(v_toConstantVal_2938_);
lean_dec(v_a_2931_);
v_name_2939_ = lean_ctor_get(v_toConstantVal_2938_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_toConstantVal_2938_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; lean_object* v_unused_3144_; 
v_unused_3143_ = lean_ctor_get(v_toConstantVal_2938_, 2);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_toConstantVal_2938_, 1);
lean_dec(v_unused_3144_);
v___x_2941_ = v_toConstantVal_2938_;
v_isShared_2942_ = v_isSharedCheck_3142_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_name_2939_);
lean_dec(v_toConstantVal_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3142_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_env_2945_; lean_object* v_nextMacroScope_2946_; lean_object* v_ngen_2947_; lean_object* v_auxDeclNGen_2948_; lean_object* v_traceState_2949_; lean_object* v_recordedDeps_2950_; lean_object* v_messages_2951_; lean_object* v_infoState_2952_; lean_object* v_snapshotTasks_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3140_; 
lean_inc(v_name_2939_);
v___x_2943_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2939_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2943_);
v___x_2944_ = lean_st_ref_take(v___y_2839_);
v_env_2945_ = lean_ctor_get(v___x_2944_, 0);
v_nextMacroScope_2946_ = lean_ctor_get(v___x_2944_, 1);
v_ngen_2947_ = lean_ctor_get(v___x_2944_, 2);
v_auxDeclNGen_2948_ = lean_ctor_get(v___x_2944_, 3);
v_traceState_2949_ = lean_ctor_get(v___x_2944_, 4);
v_recordedDeps_2950_ = lean_ctor_get(v___x_2944_, 6);
v_messages_2951_ = lean_ctor_get(v___x_2944_, 7);
v_infoState_2952_ = lean_ctor_get(v___x_2944_, 8);
v_snapshotTasks_2953_ = lean_ctor_get(v___x_2944_, 9);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_2944_, 5);
lean_dec(v_unused_3141_);
v___x_2955_ = v___x_2944_;
v_isShared_2956_ = v_isSharedCheck_3140_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_snapshotTasks_2953_);
lean_inc(v_infoState_2952_);
lean_inc(v_messages_2951_);
lean_inc(v_recordedDeps_2950_);
lean_inc(v_traceState_2949_);
lean_inc(v_auxDeclNGen_2948_);
lean_inc(v_ngen_2947_);
lean_inc(v_nextMacroScope_2946_);
lean_inc(v_env_2945_);
lean_dec(v___x_2944_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3140_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_inc(v_name_2939_);
v___x_2957_ = l_Lean_markAuxRecursor(v_env_2945_, v_name_2939_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 5, v___x_2906_);
lean_ctor_set(v___x_2955_, 0, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_nextMacroScope_2946_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_ngen_2947_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_auxDeclNGen_2948_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_traceState_2949_);
lean_ctor_set(v_reuseFailAlloc_3139_, 5, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3139_, 6, v_recordedDeps_2950_);
lean_ctor_set(v_reuseFailAlloc_3139_, 7, v_messages_2951_);
lean_ctor_set(v_reuseFailAlloc_3139_, 8, v_infoState_2952_);
lean_ctor_set(v_reuseFailAlloc_3139_, 9, v_snapshotTasks_2953_);
v___x_2959_ = v_reuseFailAlloc_3139_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_mctx_2962_; lean_object* v_zetaDeltaFVarIds_2963_; lean_object* v_postponed_2964_; lean_object* v_diag_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3137_; 
v___x_2960_ = lean_st_ref_put(v___y_2839_, v___x_2959_);
v___x_2961_ = lean_st_ref_take(v___y_2837_);
v_mctx_2962_ = lean_ctor_get(v___x_2961_, 0);
v_zetaDeltaFVarIds_2963_ = lean_ctor_get(v___x_2961_, 2);
v_postponed_2964_ = lean_ctor_get(v___x_2961_, 3);
v_diag_2965_ = lean_ctor_get(v___x_2961_, 4);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_2961_, 1);
lean_dec(v_unused_3138_);
v___x_2967_ = v___x_2961_;
v_isShared_2968_ = v_isSharedCheck_3137_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_diag_2965_);
lean_inc(v_postponed_2964_);
lean_inc(v_zetaDeltaFVarIds_2963_);
lean_inc(v_mctx_2962_);
lean_dec(v___x_2961_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3137_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v___x_2918_);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_mctx_2962_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_zetaDeltaFVarIds_2963_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_postponed_2964_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_diag_2965_);
v___x_2970_ = v_reuseFailAlloc_3136_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_env_2973_; lean_object* v_nextMacroScope_2974_; lean_object* v_ngen_2975_; lean_object* v_auxDeclNGen_2976_; lean_object* v_traceState_2977_; lean_object* v_recordedDeps_2978_; lean_object* v_messages_2979_; lean_object* v_infoState_2980_; lean_object* v_snapshotTasks_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3134_; 
v___x_2971_ = lean_st_ref_put(v___y_2837_, v___x_2970_);
v___x_2972_ = lean_st_ref_take(v___y_2839_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
v_nextMacroScope_2974_ = lean_ctor_get(v___x_2972_, 1);
v_ngen_2975_ = lean_ctor_get(v___x_2972_, 2);
v_auxDeclNGen_2976_ = lean_ctor_get(v___x_2972_, 3);
v_traceState_2977_ = lean_ctor_get(v___x_2972_, 4);
v_recordedDeps_2978_ = lean_ctor_get(v___x_2972_, 6);
v_messages_2979_ = lean_ctor_get(v___x_2972_, 7);
v_infoState_2980_ = lean_ctor_get(v___x_2972_, 8);
v_snapshotTasks_2981_ = lean_ctor_get(v___x_2972_, 9);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_2972_, 5);
lean_dec(v_unused_3135_);
v___x_2983_ = v___x_2972_;
v_isShared_2984_ = v_isSharedCheck_3134_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snapshotTasks_2981_);
lean_inc(v_infoState_2980_);
lean_inc(v_messages_2979_);
lean_inc(v_recordedDeps_2978_);
lean_inc(v_traceState_2977_);
lean_inc(v_auxDeclNGen_2976_);
lean_inc(v_ngen_2975_);
lean_inc(v_nextMacroScope_2974_);
lean_inc(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3134_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_inc(v_name_2939_);
v___x_2985_ = l_Lean_addProtected(v_env_2973_, v_name_2939_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 5, v___x_2906_);
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_nextMacroScope_2974_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_ngen_2975_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_auxDeclNGen_2976_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v_traceState_2977_);
lean_ctor_set(v_reuseFailAlloc_3133_, 5, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3133_, 6, v_recordedDeps_2978_);
lean_ctor_set(v_reuseFailAlloc_3133_, 7, v_messages_2979_);
lean_ctor_set(v_reuseFailAlloc_3133_, 8, v_infoState_2980_);
lean_ctor_set(v_reuseFailAlloc_3133_, 9, v_snapshotTasks_2981_);
v___x_2987_ = v_reuseFailAlloc_3133_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_mctx_2990_; lean_object* v_zetaDeltaFVarIds_2991_; lean_object* v_postponed_2992_; lean_object* v_diag_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3131_; 
v___x_2988_ = lean_st_ref_put(v___y_2839_, v___x_2987_);
v___x_2989_ = lean_st_ref_take(v___y_2837_);
v_mctx_2990_ = lean_ctor_get(v___x_2989_, 0);
v_zetaDeltaFVarIds_2991_ = lean_ctor_get(v___x_2989_, 2);
v_postponed_2992_ = lean_ctor_get(v___x_2989_, 3);
v_diag_2993_ = lean_ctor_get(v___x_2989_, 4);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_2989_, 1);
lean_dec(v_unused_3132_);
v___x_2995_ = v___x_2989_;
v_isShared_2996_ = v_isSharedCheck_3131_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_diag_2993_);
lean_inc(v_postponed_2992_);
lean_inc(v_zetaDeltaFVarIds_2991_);
lean_inc(v_mctx_2990_);
lean_dec(v___x_2989_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3131_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_2918_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_mctx_2990_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_zetaDeltaFVarIds_2991_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_postponed_2992_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_diag_2993_);
v___x_2998_ = v_reuseFailAlloc_3130_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2999_ = lean_st_ref_put(v___y_2837_, v___x_2998_);
v___x_3000_ = l_Lean_Expr_const___override(v_name_2939_, v___x_2831_);
v___x_3001_ = l_Lean_mkAppN(v___x_3000_, v___x_2863_);
v___x_3002_ = lean_array_get(v___x_2826_, v_fs_2835_, v_val_2827_);
lean_dec_ref(v_fs_2835_);
v___x_3003_ = l_Lean_mkAppN(v___x_3002_, v___x_2865_);
lean_dec_ref(v___x_2865_);
v___x_3004_ = l_Lean_Meta_mkPProdSndM(v___x_2923_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_Lean_Expr_app___override(v___x_3003_, v_a_3005_);
v___x_3007_ = l_Lean_Meta_mkEq(v___x_3001_, v___x_3006_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_n(v_a_3008_, 2);
lean_dec_ref_known(v___x_3007_, 1);
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3008_, v___x_3009_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = l_Lean_Expr_mvarId_x21(v_a_3011_);
v___x_3013_ = l_Lean_Expr_fvarId_x21(v___x_2824_);
lean_dec_ref(v___x_2824_);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_2833_);
v___x_3015_ = lean_box(0);
v___x_3016_ = l_Lean_MVarId_cases(v___x_3012_, v___x_3013_, v___x_3014_, v___x_2871_, v___x_3015_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; size_t v_sz_3019_; lean_object* v___x_3020_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_box(0);
v_sz_3019_ = lean_array_size(v_a_3017_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3017_, v_sz_3019_, v___x_2846_, v___x_3018_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v_a_3017_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3021_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3011_, v___y_2837_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_Meta_mkForallFVars(v___x_2863_, v_a_3008_, v___x_2871_, v___x_2828_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = l_Lean_Meta_mkLambdaFVars(v___x_2863_, v_a_3022_, v___x_2871_, v___x_2828_, v___x_2871_, v___x_2828_, v___x_2872_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2863_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc(v_brecOnEqName_2834_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 2, v_a_3024_);
lean_ctor_set(v___x_2941_, 1, v_levelParams_2830_);
lean_ctor_set(v___x_2941_, 0, v_brecOnEqName_2834_);
v___x_3028_ = v___x_2941_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_brecOnEqName_2834_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_levelParams_2830_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_a_3024_);
v___x_3028_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = lean_box(0);
lean_inc(v_brecOnEqName_2834_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set_tag(v___x_2851_, 1);
lean_ctor_set(v___x_2851_, 1, v___x_3029_);
lean_ctor_set(v___x_2851_, 0, v_brecOnEqName_2834_);
v___x_3031_ = v___x_2851_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_brecOnEqName_2834_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_2890_ == 0)
{
lean_ctor_set(v___x_2889_, 2, v___x_3031_);
lean_ctor_set(v___x_2889_, 1, v_a_3026_);
lean_ctor_set(v___x_2889_, 0, v___x_3028_);
v___x_3033_ = v___x_2889_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_a_3026_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v_a_3035_; lean_object* v___x_3036_; 
v___x_3034_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3033_, v___y_2839_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = l_Lean_addDecl(v_a_3035_, v___x_2871_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3036_, 0);
lean_dec(v_unused_3078_);
v___x_3038_ = v___x_3036_;
v_isShared_3039_ = v_isSharedCheck_3077_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v___x_3036_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3077_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v_env_3041_; lean_object* v_nextMacroScope_3042_; lean_object* v_ngen_3043_; lean_object* v_auxDeclNGen_3044_; lean_object* v_traceState_3045_; lean_object* v_recordedDeps_3046_; lean_object* v_messages_3047_; lean_object* v_infoState_3048_; lean_object* v_snapshotTasks_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3075_; 
v___x_3040_ = lean_st_ref_take(v___y_2839_);
v_env_3041_ = lean_ctor_get(v___x_3040_, 0);
v_nextMacroScope_3042_ = lean_ctor_get(v___x_3040_, 1);
v_ngen_3043_ = lean_ctor_get(v___x_3040_, 2);
v_auxDeclNGen_3044_ = lean_ctor_get(v___x_3040_, 3);
v_traceState_3045_ = lean_ctor_get(v___x_3040_, 4);
v_recordedDeps_3046_ = lean_ctor_get(v___x_3040_, 6);
v_messages_3047_ = lean_ctor_get(v___x_3040_, 7);
v_infoState_3048_ = lean_ctor_get(v___x_3040_, 8);
v_snapshotTasks_3049_ = lean_ctor_get(v___x_3040_, 9);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3040_, 5);
lean_dec(v_unused_3076_);
v___x_3051_ = v___x_3040_;
v_isShared_3052_ = v_isSharedCheck_3075_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snapshotTasks_3049_);
lean_inc(v_infoState_3048_);
lean_inc(v_messages_3047_);
lean_inc(v_recordedDeps_3046_);
lean_inc(v_traceState_3045_);
lean_inc(v_auxDeclNGen_3044_);
lean_inc(v_ngen_3043_);
lean_inc(v_nextMacroScope_3042_);
lean_inc(v_env_3041_);
lean_dec(v___x_3040_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3075_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = l_Lean_addProtected(v_env_3041_, v_brecOnEqName_2834_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 5, v___x_2906_);
lean_ctor_set(v___x_3051_, 0, v___x_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_nextMacroScope_3042_);
lean_ctor_set(v_reuseFailAlloc_3074_, 2, v_ngen_3043_);
lean_ctor_set(v_reuseFailAlloc_3074_, 3, v_auxDeclNGen_3044_);
lean_ctor_set(v_reuseFailAlloc_3074_, 4, v_traceState_3045_);
lean_ctor_set(v_reuseFailAlloc_3074_, 5, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3074_, 6, v_recordedDeps_3046_);
lean_ctor_set(v_reuseFailAlloc_3074_, 7, v_messages_3047_);
lean_ctor_set(v_reuseFailAlloc_3074_, 8, v_infoState_3048_);
lean_ctor_set(v_reuseFailAlloc_3074_, 9, v_snapshotTasks_3049_);
v___x_3055_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v_mctx_3058_; lean_object* v_zetaDeltaFVarIds_3059_; lean_object* v_postponed_3060_; lean_object* v_diag_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3072_; 
v___x_3056_ = lean_st_ref_put(v___y_2839_, v___x_3055_);
v___x_3057_ = lean_st_ref_take(v___y_2837_);
v_mctx_3058_ = lean_ctor_get(v___x_3057_, 0);
v_zetaDeltaFVarIds_3059_ = lean_ctor_get(v___x_3057_, 2);
v_postponed_3060_ = lean_ctor_get(v___x_3057_, 3);
v_diag_3061_ = lean_ctor_get(v___x_3057_, 4);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3072_ == 0)
{
lean_object* v_unused_3073_; 
v_unused_3073_ = lean_ctor_get(v___x_3057_, 1);
lean_dec(v_unused_3073_);
v___x_3063_ = v___x_3057_;
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_diag_3061_);
lean_inc(v_postponed_3060_);
lean_inc(v_zetaDeltaFVarIds_3059_);
lean_inc(v_mctx_3058_);
lean_dec(v___x_3057_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 1, v___x_2918_);
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_mctx_3058_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3071_, 2, v_zetaDeltaFVarIds_3059_);
lean_ctor_set(v_reuseFailAlloc_3071_, 3, v_postponed_3060_);
lean_ctor_set(v_reuseFailAlloc_3071_, 4, v_diag_3061_);
v___x_3066_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3067_ = lean_st_ref_put(v___y_2837_, v___x_3066_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3018_);
v___x_3069_ = v___x_3038_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3018_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2834_);
return v___x_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_a_3024_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3082_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3025_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3025_);
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
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v_a_3022_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3090_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3023_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3023_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
else
{
lean_dec(v_a_3011_);
lean_dec(v_a_3008_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
return v___x_3020_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_3011_);
lean_dec(v_a_3008_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3098_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3016_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3016_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3008_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3106_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3010_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3010_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3114_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3007_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3007_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3122_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3004_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3004_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
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
}
else
{
lean_dec(v_a_2931_);
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_2927_);
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3147_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_2928_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_2928_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3155_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_2926_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_2926_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2889_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3163_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_2924_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_2924_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
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
lean_dec(v_a_2879_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_a_2874_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3182_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_2875_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_2875_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2857_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3190_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_2873_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_2873_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2865_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2857_);
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3198_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_2869_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_2869_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_del_object(v___x_2851_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
lean_dec_ref(v___x_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2816_);
v_a_3206_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_2854_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_2854_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
lean_dec_ref(v___x_2823_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2816_);
lean_dec(v___x_2813_);
v_a_3216_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_2847_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_2847_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3224_ = _args[0];
lean_object* v_tail_3225_ = _args[1];
lean_object* v_recName_3226_ = _args[2];
lean_object* v___x_3227_ = _args[3];
lean_object* v___x_3228_ = _args[4];
lean_object* v___x_3229_ = _args[5];
lean_object* v___x_3230_ = _args[6];
lean_object* v___x_3231_ = _args[7];
lean_object* v___x_3232_ = _args[8];
lean_object* v___x_3233_ = _args[9];
lean_object* v___x_3234_ = _args[10];
lean_object* v___x_3235_ = _args[11];
lean_object* v___x_3236_ = _args[12];
lean_object* v___x_3237_ = _args[13];
lean_object* v_val_3238_ = _args[14];
lean_object* v___x_3239_ = _args[15];
lean_object* v_brecOnGoName_3240_ = _args[16];
lean_object* v_levelParams_3241_ = _args[17];
lean_object* v___x_3242_ = _args[18];
lean_object* v_brecOnName_3243_ = _args[19];
lean_object* v___x_3244_ = _args[20];
lean_object* v_brecOnEqName_3245_ = _args[21];
lean_object* v_fs_3246_ = _args[22];
lean_object* v___y_3247_ = _args[23];
lean_object* v___y_3248_ = _args[24];
lean_object* v___y_3249_ = _args[25];
lean_object* v___y_3250_ = _args[26];
lean_object* v___y_3251_ = _args[27];
_start:
{
uint8_t v___x_30857__boxed_3252_; lean_object* v_res_3253_; 
v___x_30857__boxed_3252_ = lean_unbox(v___x_3239_);
v_res_3253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3224_, v_tail_3225_, v_recName_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v___x_3231_, v___x_3232_, v___x_3233_, v___x_3234_, v___x_3235_, v___x_3236_, v___x_3237_, v_val_3238_, v___x_30857__boxed_3252_, v_brecOnGoName_3240_, v_levelParams_3241_, v___x_3242_, v_brecOnName_3243_, v___x_3244_, v_brecOnEqName_3245_, v_fs_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___x_3244_);
lean_dec(v_val_3238_);
lean_dec_ref(v___x_3237_);
lean_dec(v___x_3236_);
lean_dec_ref(v___x_3232_);
lean_dec(v___x_3231_);
lean_dec(v___x_3230_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3254_, lean_object* v_a_3255_, uint8_t v___x_3256_, lean_object* v_f_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; 
lean_inc_ref(v_targs_3254_);
v___x_3263_ = lean_array_push(v_targs_3254_, v_f_3257_);
v___x_3264_ = l_Lean_mkAppN(v_a_3255_, v_targs_3254_);
lean_dec_ref(v_targs_3254_);
v___x_3265_ = 0;
v___x_3266_ = 1;
v___x_3267_ = l_Lean_Meta_mkForallFVars(v___x_3263_, v___x_3264_, v___x_3265_, v___x_3256_, v___x_3256_, v___x_3266_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
lean_dec_ref(v___x_3263_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3268_, lean_object* v_a_3269_, lean_object* v___x_3270_, lean_object* v_f_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
uint8_t v___x_31571__boxed_3277_; lean_object* v_res_3278_; 
v___x_31571__boxed_3277_ = lean_unbox(v___x_3270_);
v_res_3278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3268_, v_a_3269_, v___x_31571__boxed_3277_, v_f_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3282_, uint8_t v___x_3283_, lean_object* v___x_3284_, lean_object* v_targs_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v___x_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3292_ = lean_box(v___x_3283_);
lean_inc_ref(v_targs_3285_);
v___f_3293_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3293_, 0, v_targs_3285_);
lean_closure_set(v___f_3293_, 1, v_a_3282_);
lean_closure_set(v___f_3293_, 2, v___x_3292_);
v___x_3294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3295_ = l_Lean_mkAppN(v___x_3284_, v_targs_3285_);
lean_dec_ref(v_targs_3285_);
v___x_3296_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3294_, v___x_3295_, v___f_3293_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3297_, lean_object* v___x_3298_, lean_object* v___x_3299_, lean_object* v_targs_3300_, lean_object* v_x_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
uint8_t v___x_31605__boxed_3307_; lean_object* v_res_3308_; 
v___x_31605__boxed_3307_ = lean_unbox(v___x_3298_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3297_, v___x_31605__boxed_3307_, v___x_3299_, v_targs_3300_, v_x_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec_ref(v_x_3301_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_a_3309_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3317_, lean_object* v_x_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_res_3324_; 
v_res_3324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3317_, v_x_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec_ref(v_x_3318_);
return v_res_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3326_, lean_object* v___x_3327_, lean_object* v_as_3328_, size_t v_sz_3329_, size_t v_i_3330_, lean_object* v_b_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
uint8_t v___x_3337_; 
v___x_3337_ = lean_usize_dec_lt(v_i_3330_, v_sz_3329_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_b_3331_);
return v___x_3338_;
}
else
{
lean_object* v_snd_3339_; lean_object* v_fst_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3437_; 
v_snd_3339_ = lean_ctor_get(v_b_3331_, 1);
v_fst_3340_ = lean_ctor_get(v_b_3331_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_b_3331_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3342_ = v_b_3331_;
v_isShared_3343_ = v_isSharedCheck_3437_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_snd_3339_);
lean_inc(v_fst_3340_);
lean_dec(v_b_3331_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3437_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v_fst_3344_; lean_object* v_snd_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3436_; 
v_fst_3344_ = lean_ctor_get(v_snd_3339_, 0);
v_snd_3345_ = lean_ctor_get(v_snd_3339_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_snd_3339_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3347_ = v_snd_3339_;
v_isShared_3348_ = v_isSharedCheck_3436_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_snd_3345_);
lean_inc(v_fst_3344_);
lean_dec(v_snd_3339_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3436_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v_next_3357_; 
v_next_3357_ = lean_ctor_get(v_snd_3345_, 0);
lean_inc(v_next_3357_);
if (lean_obj_tag(v_next_3357_) == 0)
{
goto v___jp_3349_;
}
else
{
lean_object* v_upperBound_3358_; lean_object* v_val_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3435_; 
v_upperBound_3358_ = lean_ctor_get(v_snd_3345_, 1);
v_val_3359_ = lean_ctor_get(v_next_3357_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_next_3357_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3361_ = v_next_3357_;
v_isShared_3362_ = v_isSharedCheck_3435_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_val_3359_);
lean_dec(v_next_3357_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3435_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
uint8_t v___x_3363_; 
v___x_3363_ = lean_nat_dec_lt(v_val_3359_, v_upperBound_3358_);
if (v___x_3363_ == 0)
{
lean_del_object(v___x_3361_);
lean_dec(v_val_3359_);
goto v___jp_3349_;
}
else
{
lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3432_; 
lean_inc(v_upperBound_3358_);
lean_del_object(v___x_3347_);
lean_del_object(v___x_3342_);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_snd_3345_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; 
v_unused_3433_ = lean_ctor_get(v_snd_3345_, 1);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v_snd_3345_, 0);
lean_dec(v_unused_3434_);
v___x_3365_ = v_snd_3345_;
v_isShared_3366_ = v_isSharedCheck_3432_;
goto v_resetjp_3364_;
}
else
{
lean_dec(v_snd_3345_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3432_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v_array_3367_; lean_object* v_start_3368_; lean_object* v_stop_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3373_; 
v_array_3367_ = lean_ctor_get(v_fst_3344_, 0);
v_start_3368_ = lean_ctor_get(v_fst_3344_, 1);
v_stop_3369_ = lean_ctor_get(v_fst_3344_, 2);
v___x_3370_ = lean_unsigned_to_nat(1u);
v___x_3371_ = lean_nat_add(v_val_3359_, v___x_3370_);
lean_dec(v_val_3359_);
lean_inc(v___x_3371_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3371_);
v___x_3373_ = v___x_3361_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3375_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3373_);
v___x_3375_ = v___x_3365_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3430_, 1, v_upperBound_3358_);
v___x_3375_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_nat_dec_lt(v_start_3368_, v_stop_3369_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
lean_dec(v___x_3371_);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v_fst_3344_);
lean_ctor_set(v___x_3377_, 1, v___x_3375_);
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v_fst_3340_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
return v___x_3379_;
}
else
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3426_; 
lean_inc(v_stop_3369_);
lean_inc(v_start_3368_);
lean_inc_ref(v_array_3367_);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_fst_3344_);
if (v_isSharedCheck_3426_ == 0)
{
lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; 
v_unused_3427_ = lean_ctor_get(v_fst_3344_, 2);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_fst_3344_, 1);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_fst_3344_, 0);
lean_dec(v_unused_3429_);
v___x_3381_ = v_fst_3344_;
v_isShared_3382_ = v_isSharedCheck_3426_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v_fst_3344_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3426_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
uint8_t v___x_3383_; lean_object* v_a_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3383_ = lean_nat_dec_lt(v___x_3326_, v___x_3327_);
v_a_3384_ = lean_array_uget_borrowed(v_as_3328_, v_i_3330_);
v___x_3385_ = lean_array_fget_borrowed(v_array_3367_, v_start_3368_);
v___x_3386_ = lean_box(v___x_3383_);
lean_inc(v___x_3385_);
lean_inc(v_a_3384_);
v___f_3387_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3387_, 0, v_a_3384_);
lean_closure_set(v___f_3387_, 1, v___x_3386_);
lean_closure_set(v___f_3387_, 2, v___x_3385_);
v___x_3388_ = lean_nat_add(v_start_3368_, v___x_3370_);
lean_dec(v_start_3368_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 1, v___x_3388_);
v___x_3390_ = v___x_3381_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_array_3367_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3425_, 2, v_stop_3369_);
v___x_3390_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; 
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v_a_3384_);
v___x_3391_ = lean_infer_type(v_a_3384_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = 0;
v___x_3394_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3392_, v___f_3387_, v___x_3393_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___f_3396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3396_, 0, v_a_3395_);
v___x_3397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3398_ = l_Nat_reprFast(v___x_3371_);
v___x_3399_ = lean_string_append(v___x_3397_, v___x_3398_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = lean_box(0);
v___x_3401_ = l_Lean_Name_str___override(v___x_3400_, v___x_3399_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___f_3396_);
v___x_3403_ = lean_array_push(v_fst_3340_, v___x_3402_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3390_);
lean_ctor_set(v___x_3404_, 1, v___x_3375_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3330_, v___x_3406_);
v_i_3330_ = v___x_3407_;
v_b_3331_ = v___x_3405_;
goto _start;
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec_ref(v___x_3390_);
lean_dec_ref(v___x_3375_);
lean_dec(v___x_3371_);
lean_dec(v_fst_3340_);
v_a_3409_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3394_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3394_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v___x_3390_);
lean_dec_ref(v___f_3387_);
lean_dec_ref(v___x_3375_);
lean_dec(v___x_3371_);
lean_dec(v_fst_3340_);
v_a_3417_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3391_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3391_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
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
v___jp_3349_:
{
lean_object* v___x_3351_; 
if (v_isShared_3348_ == 0)
{
v___x_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_fst_3344_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_snd_3345_);
v___x_3351_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v___x_3351_);
v___x_3353_ = v___x_3342_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_fst_3340_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3438_, lean_object* v___x_3439_, lean_object* v_as_3440_, lean_object* v_sz_3441_, lean_object* v_i_3442_, lean_object* v_b_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
size_t v_sz_boxed_3449_; size_t v_i_boxed_3450_; lean_object* v_res_3451_; 
v_sz_boxed_3449_ = lean_unbox_usize(v_sz_3441_);
lean_dec(v_sz_3441_);
v_i_boxed_3450_ = lean_unbox_usize(v_i_3442_);
lean_dec(v_i_3442_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3438_, v___x_3439_, v_as_3440_, v_sz_boxed_3449_, v_i_boxed_3450_, v_b_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v_as_3440_);
lean_dec(v___x_3439_);
lean_dec(v___x_3438_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3452_, size_t v_i_3453_, lean_object* v_bs_3454_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_lt(v_i_3453_, v_sz_3452_);
if (v___x_3455_ == 0)
{
return v_bs_3454_;
}
else
{
lean_object* v_v_3456_; lean_object* v_fst_3457_; lean_object* v_snd_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3474_; 
v_v_3456_ = lean_array_uget(v_bs_3454_, v_i_3453_);
v_fst_3457_ = lean_ctor_get(v_v_3456_, 0);
v_snd_3458_ = lean_ctor_get(v_v_3456_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_v_3456_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3460_ = v_v_3456_;
v_isShared_3461_ = v_isSharedCheck_3474_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_snd_3458_);
lean_inc(v_fst_3457_);
lean_dec(v_v_3456_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3474_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v_bs_x27_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3462_ = lean_unsigned_to_nat(0u);
v_bs_x27_3463_ = lean_array_uset(v_bs_3454_, v_i_3453_, v___x_3462_);
v___x_3464_ = 0;
v___x_3465_ = lean_box(v___x_3464_);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3465_);
v___x_3467_ = v___x_3460_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_snd_3458_);
v___x_3467_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; size_t v___x_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v___x_3468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_fst_3457_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = ((size_t)1ULL);
v___x_3470_ = lean_usize_add(v_i_3453_, v___x_3469_);
v___x_3471_ = lean_array_uset(v_bs_x27_3463_, v_i_3453_, v___x_3468_);
v_i_3453_ = v___x_3470_;
v_bs_3454_ = v___x_3471_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3475_, lean_object* v_i_3476_, lean_object* v_bs_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3475_);
lean_dec(v_sz_3475_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3476_);
lean_dec(v_i_3476_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3478_, v_i_boxed_3479_, v_bs_3477_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v_a_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_30400__overap_3489_; lean_object* v___x_3490_; 
v___x_30400__overap_3489_ = l_instInhabitedOfMonad___redArg(v___x_3481_, v___x_3482_);
lean_inc(v___y_3487_);
lean_inc_ref(v___y_3486_);
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
v___x_3490_ = lean_apply_5(v___x_30400__overap_3489_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, lean_box(0));
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3491_, lean_object* v___x_3492_, lean_object* v_a_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3491_, v___x_3492_, v_a_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec_ref(v_a_3493_);
return v_res_3499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_instMonadEIO___redArg();
return v___x_3500_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3502_ = l_StateRefT_x27_instMonad___redArg(v___x_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3507_, lean_object* v_declInfos_3508_, lean_object* v_k_3509_, lean_object* v_kind_3510_, lean_object* v_b_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_kind_boxed_3517_; lean_object* v_res_3518_; 
v_kind_boxed_3517_ = lean_unbox(v_kind_3510_);
v_res_3518_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3507_, v_declInfos_3508_, v_k_3509_, v_kind_boxed_3517_, v_b_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3519_, lean_object* v_declInfos_3520_, lean_object* v_k_3521_, uint8_t v_kind_3522_, lean_object* v_name_3523_, uint8_t v_bi_3524_, lean_object* v_type_3525_, uint8_t v_kind_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; lean_object* v___f_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_box(v_kind_3522_);
v___f_3533_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3533_, 0, v_acc_3519_);
lean_closure_set(v___f_3533_, 1, v_declInfos_3520_);
lean_closure_set(v___f_3533_, 2, v_k_3521_);
lean_closure_set(v___f_3533_, 3, v___x_3532_);
v___x_3534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3523_, v_bi_3524_, v_type_3525_, v___f_3533_, v_kind_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
v_a_3543_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3534_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3534_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3551_, lean_object* v_k_3552_, uint8_t v_kind_3553_, lean_object* v_acc_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; lean_object* v_toApplicative_3561_; lean_object* v_toFunctor_3562_; lean_object* v_toSeq_3563_; lean_object* v_toSeqLeft_3564_; lean_object* v_toSeqRight_3565_; lean_object* v___f_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; lean_object* v___f_3571_; lean_object* v___f_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v_toApplicative_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3633_; 
v___x_3560_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3561_ = lean_ctor_get(v___x_3560_, 0);
v_toFunctor_3562_ = lean_ctor_get(v_toApplicative_3561_, 0);
v_toSeq_3563_ = lean_ctor_get(v_toApplicative_3561_, 2);
v_toSeqLeft_3564_ = lean_ctor_get(v_toApplicative_3561_, 3);
v_toSeqRight_3565_ = lean_ctor_get(v_toApplicative_3561_, 4);
v___f_3566_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3567_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3562_, 2);
v___f_3568_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3568_, 0, v_toFunctor_3562_);
v___f_3569_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3569_, 0, v_toFunctor_3562_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___f_3568_);
lean_ctor_set(v___x_3570_, 1, v___f_3569_);
lean_inc(v_toSeqRight_3565_);
v___f_3571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3571_, 0, v_toSeqRight_3565_);
lean_inc(v_toSeqLeft_3564_);
v___f_3572_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3572_, 0, v_toSeqLeft_3564_);
lean_inc(v_toSeq_3563_);
v___f_3573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3573_, 0, v_toSeq_3563_);
v___x_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3570_);
lean_ctor_set(v___x_3574_, 1, v___f_3566_);
lean_ctor_set(v___x_3574_, 2, v___f_3573_);
lean_ctor_set(v___x_3574_, 3, v___f_3572_);
lean_ctor_set(v___x_3574_, 4, v___f_3571_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v___f_3567_);
v___x_3576_ = l_StateRefT_x27_instMonad___redArg(v___x_3575_);
v_toApplicative_3577_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v___x_3576_, 1);
lean_dec(v_unused_3634_);
v___x_3579_ = v___x_3576_;
v_isShared_3580_ = v_isSharedCheck_3633_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_toApplicative_3577_);
lean_dec(v___x_3576_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3633_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v_toFunctor_3581_; lean_object* v_toSeq_3582_; lean_object* v_toSeqLeft_3583_; lean_object* v_toSeqRight_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3631_; 
v_toFunctor_3581_ = lean_ctor_get(v_toApplicative_3577_, 0);
v_toSeq_3582_ = lean_ctor_get(v_toApplicative_3577_, 2);
v_toSeqLeft_3583_ = lean_ctor_get(v_toApplicative_3577_, 3);
v_toSeqRight_3584_ = lean_ctor_get(v_toApplicative_3577_, 4);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_toApplicative_3577_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v_toApplicative_3577_, 1);
lean_dec(v_unused_3632_);
v___x_3586_ = v_toApplicative_3577_;
v_isShared_3587_ = v_isSharedCheck_3631_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_toSeqRight_3584_);
lean_inc(v_toSeqLeft_3583_);
lean_inc(v_toSeq_3582_);
lean_inc(v_toFunctor_3581_);
lean_dec(v_toApplicative_3577_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3631_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___f_3594_; lean_object* v___f_3595_; lean_object* v___x_3597_; 
v___f_3588_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3589_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3581_);
v___f_3590_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3590_, 0, v_toFunctor_3581_);
v___f_3591_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3591_, 0, v_toFunctor_3581_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___f_3590_);
lean_ctor_set(v___x_3592_, 1, v___f_3591_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toSeqRight_3584_);
v___f_3594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3594_, 0, v_toSeqLeft_3583_);
v___f_3595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3595_, 0, v_toSeq_3582_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 4, v___f_3593_);
lean_ctor_set(v___x_3586_, 3, v___f_3594_);
lean_ctor_set(v___x_3586_, 2, v___f_3595_);
lean_ctor_set(v___x_3586_, 1, v___f_3588_);
lean_ctor_set(v___x_3586_, 0, v___x_3592_);
v___x_3597_ = v___x_3586_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v___f_3588_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v___f_3595_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v___f_3594_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v___f_3593_);
v___x_3597_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3599_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v___f_3589_);
lean_ctor_set(v___x_3579_, 0, v___x_3597_);
v___x_3599_ = v___x_3579_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___f_3589_);
v___x_3599_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v___x_3600_ = lean_array_get_size(v_acc_3554_);
v___x_3601_ = lean_array_get_size(v_declInfos_3551_);
v___x_3602_ = lean_nat_dec_lt(v___x_3600_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; 
lean_dec_ref(v___x_3599_);
lean_dec_ref(v_declInfos_3551_);
lean_inc(v___y_3558_);
lean_inc_ref(v___y_3557_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
v___x_3603_ = lean_apply_6(v_k_3552_, v_acc_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, lean_box(0));
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; uint8_t v___x_3605_; lean_object* v___x_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v_snd_3613_; lean_object* v_fst_3614_; lean_object* v_fst_3615_; lean_object* v_snd_3616_; lean_object* v___x_3617_; 
v___x_3604_ = lean_box(0);
v___x_3605_ = 0;
v___x_3606_ = l_Lean_instInhabitedExpr;
v___f_3607_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3607_, 0, v___x_3599_);
lean_closure_set(v___f_3607_, 1, v___x_3606_);
v___f_3608_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3608_, 0, v___f_3607_);
v___x_3609_ = lean_box(v___x_3605_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v___f_3608_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3604_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_array_get(v___x_3611_, v_declInfos_3551_, v___x_3600_);
lean_dec_ref_known(v___x_3611_, 2);
v_snd_3613_ = lean_ctor_get(v___x_3612_, 1);
lean_inc(v_snd_3613_);
v_fst_3614_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_fst_3614_);
lean_dec(v___x_3612_);
v_fst_3615_ = lean_ctor_get(v_snd_3613_, 0);
lean_inc(v_fst_3615_);
v_snd_3616_ = lean_ctor_get(v_snd_3613_, 1);
lean_inc(v_snd_3616_);
lean_dec(v_snd_3613_);
lean_inc(v___y_3558_);
lean_inc_ref(v___y_3557_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
lean_inc_ref(v_acc_3554_);
v___x_3617_ = lean_apply_6(v_snd_3616_, v_acc_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, lean_box(0));
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v___x_3619_ = lean_unbox(v_fst_3615_);
lean_dec(v_fst_3615_);
v___x_3620_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3554_, v_declInfos_3551_, v_k_3552_, v_kind_3553_, v_fst_3614_, v___x_3619_, v_a_3618_, v_kind_3553_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v___x_3620_;
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_fst_3615_);
lean_dec(v_fst_3614_);
lean_dec_ref(v_acc_3554_);
lean_dec_ref(v_k_3552_);
lean_dec_ref(v_declInfos_3551_);
v_a_3621_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3617_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3617_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3635_, lean_object* v_declInfos_3636_, lean_object* v_k_3637_, uint8_t v_kind_3638_, lean_object* v_b_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = lean_array_push(v_acc_3635_, v_b_3639_);
v___x_3646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3636_, v_k_3637_, v_kind_3638_, v___x_3645_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3647_, lean_object* v_declInfos_3648_, lean_object* v_k_3649_, lean_object* v_kind_3650_, lean_object* v_name_3651_, lean_object* v_bi_3652_, lean_object* v_type_3653_, lean_object* v_kind_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
uint8_t v_kind_boxed_3660_; uint8_t v_bi_boxed_3661_; uint8_t v_kind_boxed_3662_; lean_object* v_res_3663_; 
v_kind_boxed_3660_ = lean_unbox(v_kind_3650_);
v_bi_boxed_3661_ = lean_unbox(v_bi_3652_);
v_kind_boxed_3662_ = lean_unbox(v_kind_3654_);
v_res_3663_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3647_, v_declInfos_3648_, v_k_3649_, v_kind_boxed_3660_, v_name_3651_, v_bi_boxed_3661_, v_type_3653_, v_kind_boxed_3662_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3664_, lean_object* v_k_3665_, lean_object* v_kind_3666_, lean_object* v_acc_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_kind_boxed_3673_; lean_object* v_res_3674_; 
v_kind_boxed_3673_ = lean_unbox(v_kind_3666_);
v_res_3674_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3664_, v_k_3665_, v_kind_boxed_3673_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3675_, lean_object* v_k_3676_, uint8_t v_kind_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3684_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3675_, v_k_3676_, v_kind_3677_, v___x_3683_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3685_, lean_object* v_k_3686_, lean_object* v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
uint8_t v_kind_boxed_3693_; lean_object* v_res_3694_; 
v_kind_boxed_3693_ = lean_unbox(v_kind_3687_);
v_res_3694_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3685_, v_k_3686_, v_kind_boxed_3693_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3695_, lean_object* v_k_3696_, uint8_t v_kind_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
size_t v_sz_3703_; size_t v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_sz_3703_ = lean_array_size(v_declInfos_3695_);
v___x_3704_ = ((size_t)0ULL);
v___x_3705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3703_, v___x_3704_, v_declInfos_3695_);
v___x_3706_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3705_, v_k_3696_, v_kind_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3707_, lean_object* v_k_3708_, lean_object* v_kind_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_kind_boxed_3715_; lean_object* v_res_3716_; 
v_kind_boxed_3715_ = lean_unbox(v_kind_3709_);
v_res_3716_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3707_, v_k_3708_, v_kind_boxed_3715_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
return v_res_3716_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3718_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3719_ = lean_unsigned_to_nat(4u);
v___x_3720_ = lean_unsigned_to_nat(202u);
v___x_3721_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3723_ = l_mkPanicMessageWithDecl(v___x_3722_, v___x_3721_, v___x_3720_, v___x_3719_, v___x_3718_);
return v___x_3723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
return v___x_3730_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3733_ = l_Lean_stringToMessageData(v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3734_, lean_object* v_numMotives_3735_, lean_object* v_numMinors_3736_, lean_object* v___x_3737_, lean_object* v_all_3738_, lean_object* v___x_3739_, lean_object* v___x_3740_, lean_object* v_head_3741_, lean_object* v_tail_3742_, lean_object* v_recName_3743_, lean_object* v_brecOnGoName_3744_, lean_object* v_levelParams_3745_, lean_object* v_brecOnName_3746_, lean_object* v_brecOnEqName_3747_, lean_object* v_type_3748_, lean_object* v_refArgs_3749_, lean_object* v_refBody_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3756_ = lean_nat_add(v_nParams_3734_, v_numMotives_3735_);
v___x_3757_ = lean_nat_add(v___x_3756_, v_numMinors_3736_);
v___x_3758_ = lean_array_get_size(v_refArgs_3749_);
v___x_3759_ = lean_nat_dec_lt(v___x_3757_, v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
lean_dec(v___x_3757_);
lean_dec(v___x_3756_);
lean_dec_ref(v_refArgs_3749_);
lean_dec_ref(v_type_3748_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3739_);
lean_dec_ref(v_all_3738_);
lean_dec(v___x_3737_);
lean_dec(v_nParams_3734_);
v___x_3760_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3761_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3760_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3762_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3734_);
lean_inc_ref_n(v_refArgs_3749_, 2);
v___x_3763_ = l_Array_toSubarray___redArg(v_refArgs_3749_, v___x_3762_, v_nParams_3734_);
lean_inc(v___x_3756_);
v___x_3764_ = l_Array_toSubarray___redArg(v_refArgs_3749_, v_nParams_3734_, v___x_3756_);
v___x_3765_ = l_Subarray_copy___redArg(v___x_3764_);
v___x_3766_ = l_Lean_Expr_getAppFn(v_refBody_3750_);
v___x_3767_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3765_, v___x_3766_);
lean_dec_ref(v___x_3766_);
if (lean_obj_tag(v___x_3767_) == 1)
{
lean_object* v_val_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
lean_dec_ref(v_type_3748_);
v_val_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v___x_3767_, 1);
lean_inc_n(v___x_3757_, 2);
lean_inc_ref_n(v_refArgs_3749_, 2);
v___x_3769_ = l_Array_toSubarray___redArg(v_refArgs_3749_, v___x_3756_, v___x_3757_);
v___x_3770_ = l_Subarray_copy___redArg(v___x_3763_);
v___x_3771_ = l_Subarray_copy___redArg(v___x_3769_);
v___x_3772_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3765_);
lean_inc_ref(v___x_3770_);
lean_inc(v___x_3737_);
v___f_3773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3773_, 0, v___x_3737_);
lean_closure_set(v___f_3773_, 1, v___x_3770_);
lean_closure_set(v___f_3773_, 2, v___x_3765_);
lean_closure_set(v___f_3773_, 3, v_all_3738_);
lean_closure_set(v___f_3773_, 4, v___x_3739_);
lean_closure_set(v___f_3773_, 5, v___x_3762_);
lean_closure_set(v___f_3773_, 6, v___x_3772_);
v___x_3774_ = lean_nat_sub(v___x_3758_, v___x_3772_);
lean_inc(v___x_3774_);
v___x_3775_ = l_Array_toSubarray___redArg(v_refArgs_3749_, v___x_3757_, v___x_3774_);
v___x_3776_ = l_Subarray_copy___redArg(v___x_3775_);
v___x_3777_ = lean_array_get(v___x_3740_, v_refArgs_3749_, v___x_3774_);
lean_dec(v___x_3774_);
lean_dec_ref(v_refArgs_3749_);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___x_3777_);
v___x_3778_ = lean_infer_type(v___x_3777_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
lean_inc(v___y_3754_);
lean_inc_ref(v___y_3753_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
v___x_3780_ = lean_infer_type(v_a_3779_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3781_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
if (lean_obj_tag(v_a_3783_) == 1)
{
lean_object* v_val_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___f_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; size_t v_sz_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v_val_3784_ = lean_ctor_get(v_a_3783_, 0);
lean_inc(v_val_3784_);
lean_dec_ref_known(v_a_3783_, 1);
v___x_3785_ = l_Lean_mkLevelMax(v_val_3784_, v_head_3741_);
v___x_3786_ = lean_array_get_size(v___x_3765_);
v___x_3787_ = l_Array_ofFn___redArg(v___x_3786_, v___f_3773_);
v___x_3788_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3789_ = lean_array_get_size(v___x_3787_);
lean_inc_ref(v___x_3787_);
v___x_3790_ = l_Array_toSubarray___redArg(v___x_3787_, v___x_3762_, v___x_3789_);
v___x_3791_ = lean_box(v___x_3759_);
lean_inc(v___x_3757_);
lean_inc_ref(v___x_3765_);
lean_inc_ref(v___x_3790_);
v___f_3792_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3792_, 0, v___x_3785_);
lean_closure_set(v___f_3792_, 1, v_tail_3742_);
lean_closure_set(v___f_3792_, 2, v_recName_3743_);
lean_closure_set(v___f_3792_, 3, v___x_3770_);
lean_closure_set(v___f_3792_, 4, v___x_3790_);
lean_closure_set(v___f_3792_, 5, v___x_3765_);
lean_closure_set(v___f_3792_, 6, v___x_3757_);
lean_closure_set(v___f_3792_, 7, v___x_3758_);
lean_closure_set(v___f_3792_, 8, v___x_3771_);
lean_closure_set(v___f_3792_, 9, v___x_3787_);
lean_closure_set(v___f_3792_, 10, v___x_3776_);
lean_closure_set(v___f_3792_, 11, v___x_3777_);
lean_closure_set(v___f_3792_, 12, v___x_3772_);
lean_closure_set(v___f_3792_, 13, v___x_3740_);
lean_closure_set(v___f_3792_, 14, v_val_3768_);
lean_closure_set(v___f_3792_, 15, v___x_3791_);
lean_closure_set(v___f_3792_, 16, v_brecOnGoName_3744_);
lean_closure_set(v___f_3792_, 17, v_levelParams_3745_);
lean_closure_set(v___f_3792_, 18, v___x_3737_);
lean_closure_set(v___f_3792_, 19, v_brecOnName_3746_);
lean_closure_set(v___f_3792_, 20, v___x_3762_);
lean_closure_set(v___f_3792_, 21, v_brecOnEqName_3747_);
v___x_3793_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v___x_3786_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3790_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3788_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v_sz_3797_ = lean_array_size(v___x_3765_);
v___x_3798_ = ((size_t)0ULL);
v___x_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3757_, v___x_3758_, v___x_3765_, v_sz_3797_, v___x_3798_, v___x_3796_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec_ref(v___x_3765_);
lean_dec(v___x_3757_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v_fst_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v_fst_3801_ = lean_ctor_get(v_a_3800_, 0);
lean_inc(v_fst_3801_);
lean_dec(v_a_3800_);
v___x_3802_ = 0;
v___x_3803_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3801_, v___f_3792_, v___x_3802_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3803_;
}
else
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3811_; 
lean_dec_ref(v___f_3792_);
v_a_3804_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3806_ = v___x_3799_;
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3799_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3811_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3809_; 
if (v_isShared_3807_ == 0)
{
v___x_3809_ = v___x_3806_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_dec(v_a_3783_);
lean_dec_ref(v___x_3776_);
lean_dec_ref(v___f_3773_);
lean_dec_ref(v___x_3771_);
lean_dec_ref(v___x_3770_);
lean_dec(v_val_3768_);
lean_dec_ref(v___x_3765_);
lean_dec(v___x_3757_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3737_);
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3813_ = l_Lean_MessageData_ofExpr(v___x_3777_);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3816_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3817_;
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v___x_3777_);
lean_dec_ref(v___x_3776_);
lean_dec_ref(v___f_3773_);
lean_dec_ref(v___x_3771_);
lean_dec_ref(v___x_3770_);
lean_dec(v_val_3768_);
lean_dec_ref(v___x_3765_);
lean_dec(v___x_3757_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3737_);
v_a_3818_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3782_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3782_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v___x_3777_);
lean_dec_ref(v___x_3776_);
lean_dec_ref(v___f_3773_);
lean_dec_ref(v___x_3771_);
lean_dec_ref(v___x_3770_);
lean_dec(v_val_3768_);
lean_dec_ref(v___x_3765_);
lean_dec(v___x_3757_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3737_);
v_a_3826_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3780_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3780_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v___x_3777_);
lean_dec_ref(v___x_3776_);
lean_dec_ref(v___f_3773_);
lean_dec_ref(v___x_3771_);
lean_dec_ref(v___x_3770_);
lean_dec(v_val_3768_);
lean_dec_ref(v___x_3765_);
lean_dec(v___x_3757_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3737_);
v_a_3834_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3778_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3778_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_dec(v___x_3767_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3757_);
lean_dec(v___x_3756_);
lean_dec_ref(v_refArgs_3749_);
lean_dec(v_brecOnEqName_3747_);
lean_dec(v_brecOnName_3746_);
lean_dec(v_levelParams_3745_);
lean_dec(v_brecOnGoName_3744_);
lean_dec(v_recName_3743_);
lean_dec(v_tail_3742_);
lean_dec(v_head_3741_);
lean_dec_ref(v___x_3740_);
lean_dec(v___x_3739_);
lean_dec_ref(v_all_3738_);
lean_dec(v___x_3737_);
v___x_3842_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3843_ = l_Lean_MessageData_ofExpr(v_type_3748_);
v___x_3844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = lean_array_to_list(v___x_3765_);
v___x_3848_ = lean_box(0);
v___x_3849_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3847_, v___x_3848_);
v___x_3850_ = l_Lean_MessageData_ofList(v___x_3849_);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3846_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3851_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3853_ = _args[0];
lean_object* v_numMotives_3854_ = _args[1];
lean_object* v_numMinors_3855_ = _args[2];
lean_object* v___x_3856_ = _args[3];
lean_object* v_all_3857_ = _args[4];
lean_object* v___x_3858_ = _args[5];
lean_object* v___x_3859_ = _args[6];
lean_object* v_head_3860_ = _args[7];
lean_object* v_tail_3861_ = _args[8];
lean_object* v_recName_3862_ = _args[9];
lean_object* v_brecOnGoName_3863_ = _args[10];
lean_object* v_levelParams_3864_ = _args[11];
lean_object* v_brecOnName_3865_ = _args[12];
lean_object* v_brecOnEqName_3866_ = _args[13];
lean_object* v_type_3867_ = _args[14];
lean_object* v_refArgs_3868_ = _args[15];
lean_object* v_refBody_3869_ = _args[16];
lean_object* v___y_3870_ = _args[17];
lean_object* v___y_3871_ = _args[18];
lean_object* v___y_3872_ = _args[19];
lean_object* v___y_3873_ = _args[20];
lean_object* v___y_3874_ = _args[21];
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3853_, v_numMotives_3854_, v_numMinors_3855_, v___x_3856_, v_all_3857_, v___x_3858_, v___x_3859_, v_head_3860_, v_tail_3861_, v_recName_3862_, v_brecOnGoName_3863_, v_levelParams_3864_, v_brecOnName_3865_, v_brecOnEqName_3866_, v_type_3867_, v_refArgs_3868_, v_refBody_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v_refBody_3869_);
lean_dec(v_numMinors_3855_);
lean_dec(v_numMotives_3854_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3878_, lean_object* v_nParams_3879_, lean_object* v_all_3880_, lean_object* v_brecOnName_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v_brecOnGoName_3890_; lean_object* v___x_3891_; lean_object* v_brecOnEqName_3892_; lean_object* v___x_3893_; 
v___x_3887_ = l_Lean_instInhabitedExpr;
v___x_3888_ = lean_box(0);
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3881_, 2);
v_brecOnGoName_3890_ = l_Lean_Name_str___override(v_brecOnName_3881_, v___x_3889_);
v___x_3891_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3892_ = l_Lean_Name_str___override(v_brecOnName_3881_, v___x_3891_);
lean_inc(v_recName_3878_);
v___x_3893_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3878_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3921_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3896_ = v___x_3893_;
v_isShared_3897_ = v_isSharedCheck_3921_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3921_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
if (lean_obj_tag(v_a_3894_) == 7)
{
lean_object* v_val_3898_; lean_object* v_toConstantVal_3899_; lean_object* v_numMotives_3900_; lean_object* v_numMinors_3901_; lean_object* v_levelParams_3902_; lean_object* v_type_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_del_object(v___x_3896_);
v_val_3898_ = lean_ctor_get(v_a_3894_, 0);
lean_inc_ref(v_val_3898_);
lean_dec_ref_known(v_a_3894_, 1);
v_toConstantVal_3899_ = lean_ctor_get(v_val_3898_, 0);
lean_inc_ref(v_toConstantVal_3899_);
v_numMotives_3900_ = lean_ctor_get(v_val_3898_, 4);
lean_inc(v_numMotives_3900_);
v_numMinors_3901_ = lean_ctor_get(v_val_3898_, 5);
lean_inc(v_numMinors_3901_);
lean_dec_ref(v_val_3898_);
v_levelParams_3902_ = lean_ctor_get(v_toConstantVal_3899_, 1);
lean_inc_n(v_levelParams_3902_, 2);
v_type_3903_ = lean_ctor_get(v_toConstantVal_3899_, 2);
lean_inc_ref(v_type_3903_);
lean_dec_ref(v_toConstantVal_3899_);
v___x_3904_ = lean_box(0);
v___x_3905_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3902_, v___x_3904_);
if (lean_obj_tag(v___x_3905_) == 1)
{
lean_object* v_head_3906_; lean_object* v_tail_3907_; lean_object* v___f_3908_; uint8_t v___x_3909_; lean_object* v___x_3910_; 
v_head_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_head_3906_);
v_tail_3907_ = lean_ctor_get(v___x_3905_, 1);
lean_inc(v_tail_3907_);
lean_inc_ref(v_type_3903_);
v___f_3908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3908_, 0, v_nParams_3879_);
lean_closure_set(v___f_3908_, 1, v_numMotives_3900_);
lean_closure_set(v___f_3908_, 2, v_numMinors_3901_);
lean_closure_set(v___f_3908_, 3, v___x_3905_);
lean_closure_set(v___f_3908_, 4, v_all_3880_);
lean_closure_set(v___f_3908_, 5, v___x_3888_);
lean_closure_set(v___f_3908_, 6, v___x_3887_);
lean_closure_set(v___f_3908_, 7, v_head_3906_);
lean_closure_set(v___f_3908_, 8, v_tail_3907_);
lean_closure_set(v___f_3908_, 9, v_recName_3878_);
lean_closure_set(v___f_3908_, 10, v_brecOnGoName_3890_);
lean_closure_set(v___f_3908_, 11, v_levelParams_3902_);
lean_closure_set(v___f_3908_, 12, v_brecOnName_3881_);
lean_closure_set(v___f_3908_, 13, v_brecOnEqName_3892_);
lean_closure_set(v___f_3908_, 14, v_type_3903_);
v___x_3909_ = 0;
v___x_3910_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3903_, v___f_3908_, v___x_3909_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec(v___x_3905_);
lean_dec_ref(v_type_3903_);
lean_dec(v_levelParams_3902_);
lean_dec(v_numMinors_3901_);
lean_dec(v_numMotives_3900_);
lean_dec(v_brecOnEqName_3892_);
lean_dec(v_brecOnGoName_3890_);
lean_dec(v_brecOnName_3881_);
lean_dec_ref(v_all_3880_);
lean_dec(v_nParams_3879_);
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3912_ = l_Lean_MessageData_ofName(v_recName_3878_);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3915_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v___x_3916_;
}
}
else
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec(v_a_3894_);
lean_dec(v_brecOnEqName_3892_);
lean_dec(v_brecOnGoName_3890_);
lean_dec(v_brecOnName_3881_);
lean_dec_ref(v_all_3880_);
lean_dec(v_nParams_3879_);
lean_dec(v_recName_3878_);
v___x_3917_ = lean_box(0);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3917_);
v___x_3919_ = v___x_3896_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec(v_brecOnEqName_3892_);
lean_dec(v_brecOnGoName_3890_);
lean_dec(v_brecOnName_3881_);
lean_dec_ref(v_all_3880_);
lean_dec(v_nParams_3879_);
lean_dec(v_recName_3878_);
v_a_3922_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3893_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3893_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3930_, lean_object* v_nParams_3931_, lean_object* v_all_3932_, lean_object* v_brecOnName_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3930_, v_nParams_3931_, v_all_3932_, v_brecOnName_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v___x_3943_, lean_object* v___x_3944_, lean_object* v_a_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_nat_dec_lt(v_a_3945_, v_upperBound_3940_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec(v_a_3945_);
lean_dec_ref(v___x_3944_);
lean_dec(v___x_3943_);
lean_dec(v___x_3942_);
lean_dec(v___x_3941_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_b_3946_);
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = lean_unsigned_to_nat(1u);
v___x_3956_ = lean_nat_add(v_a_3945_, v___x_3955_);
lean_dec(v_a_3945_);
lean_inc_n(v___x_3956_, 2);
lean_inc(v___x_3941_);
v___x_3957_ = lean_name_append_index_after(v___x_3941_, v___x_3956_);
lean_inc(v___x_3942_);
v___x_3958_ = lean_name_append_index_after(v___x_3942_, v___x_3956_);
lean_inc_ref(v___x_3944_);
lean_inc(v___x_3943_);
v___x_3959_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3957_, v___x_3943_, v___x_3944_, v___x_3958_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_dec_ref_known(v___x_3959_, 1);
v_a_3945_ = v___x_3956_;
v_b_3946_ = v___x_3954_;
goto _start;
}
else
{
lean_dec(v___x_3956_);
lean_dec_ref(v___x_3944_);
lean_dec(v___x_3943_);
lean_dec(v___x_3942_);
lean_dec(v___x_3941_);
return v___x_3959_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v___x_3964_, lean_object* v___x_3965_, lean_object* v_a_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3961_, v___x_3962_, v___x_3963_, v___x_3964_, v___x_3965_, v_a_3966_, v_b_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_upperBound_3961_);
return v_res_3973_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3979_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3980_ = l_Lean_Name_append(v___x_3979_, v___x_3978_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_){
_start:
{
lean_object* v_toCold_3987_; lean_object* v_options_3988_; lean_object* v_inheritedTraceOptions_3989_; uint8_t v_hasTrace_3990_; lean_object* v___x_3991_; 
v_toCold_3987_ = lean_ctor_get(v_a_3984_, 0);
v_options_3988_ = lean_ctor_get(v_toCold_3987_, 2);
v_inheritedTraceOptions_3989_ = lean_ctor_get(v_toCold_3987_, 11);
v_hasTrace_3990_ = lean_ctor_get_uint8(v_options_3988_, sizeof(void*)*1);
v___x_3991_ = lean_box(0);
if (v_hasTrace_3990_ == 0)
{
lean_object* v___x_3992_; 
lean_inc(v_indName_3981_);
v___x_3992_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4057_; 
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_3995_ = v___x_3992_;
v_isShared_3996_ = v_isSharedCheck_4057_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3992_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4057_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
if (lean_obj_tag(v_a_3993_) == 5)
{
lean_object* v_val_3997_; uint8_t v_isRec_3998_; 
v_val_3997_ = lean_ctor_get(v_a_3993_, 0);
lean_inc_ref(v_val_3997_);
lean_dec_ref_known(v_a_3993_, 1);
v_isRec_3998_ = lean_ctor_get_uint8(v_val_3997_, sizeof(void*)*6);
if (v_isRec_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4001_; 
lean_dec_ref(v_val_3997_);
lean_dec(v_indName_3981_);
v___x_3999_ = lean_box(0);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_3999_);
v___x_4001_ = v___x_3995_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3999_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
else
{
lean_object* v_toConstantVal_4003_; lean_object* v_numParams_4004_; lean_object* v_all_4005_; lean_object* v_numNested_4006_; lean_object* v_type_4007_; lean_object* v___x_4008_; 
lean_del_object(v___x_3995_);
v_toConstantVal_4003_ = lean_ctor_get(v_val_3997_, 0);
lean_inc_ref(v_toConstantVal_4003_);
v_numParams_4004_ = lean_ctor_get(v_val_3997_, 1);
lean_inc(v_numParams_4004_);
v_all_4005_ = lean_ctor_get(v_val_3997_, 3);
lean_inc(v_all_4005_);
v_numNested_4006_ = lean_ctor_get(v_val_3997_, 5);
lean_inc(v_numNested_4006_);
lean_dec_ref(v_val_3997_);
v_type_4007_ = lean_ctor_get(v_toConstantVal_4003_, 2);
lean_inc_ref(v_type_4007_);
lean_dec_ref(v_toConstantVal_4003_);
v___x_4008_ = l_Lean_Meta_isPropFormerType(v_type_4007_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4044_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4011_ = v___x_4008_;
v_isShared_4012_ = v_isSharedCheck_4044_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4044_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_unbox(v_a_4009_);
lean_dec(v_a_4009_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
lean_del_object(v___x_4011_);
lean_inc_n(v_indName_3981_, 2);
v___x_4014_ = l_Lean_mkRecName(v_indName_3981_);
v___x_4015_ = l_Lean_mkBRecOnName(v_indName_3981_);
lean_inc(v_all_4005_);
v___x_4016_ = lean_array_mk(v_all_4005_);
lean_inc(v___x_4015_);
lean_inc_ref(v___x_4016_);
lean_inc(v_numParams_4004_);
lean_inc(v___x_4014_);
v___x_4017_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4014_, v_numParams_4004_, v___x_4016_, v___x_4015_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4038_; 
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4038_ == 0)
{
lean_object* v_unused_4039_; 
v_unused_4039_ = lean_ctor_get(v___x_4017_, 0);
lean_dec(v_unused_4039_);
v___x_4019_ = v___x_4017_;
v_isShared_4020_ = v_isSharedCheck_4038_;
goto v_resetjp_4018_;
}
else
{
lean_dec(v___x_4017_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4038_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4021_ = lean_unsigned_to_nat(0u);
v___x_4022_ = l_List_get_x21Internal___redArg(v___x_3991_, v_all_4005_, v___x_4021_);
lean_dec(v_all_4005_);
v___x_4023_ = lean_name_eq(v___x_4022_, v_indName_3981_);
lean_dec(v_indName_3981_);
lean_dec(v___x_4022_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
lean_dec_ref(v___x_4016_);
lean_dec(v___x_4015_);
lean_dec(v___x_4014_);
lean_dec(v_numNested_4006_);
lean_dec(v_numParams_4004_);
v___x_4024_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4024_);
v___x_4026_ = v___x_4019_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
else
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
lean_del_object(v___x_4019_);
v___x_4028_ = lean_box(0);
v___x_4029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4006_, v___x_4014_, v___x_4015_, v_numParams_4004_, v___x_4016_, v___x_4021_, v___x_4028_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_numNested_4006_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; 
v_unused_4037_ = lean_ctor_get(v___x_4029_, 0);
lean_dec(v_unused_4037_);
v___x_4031_ = v___x_4029_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_dec(v___x_4029_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4028_);
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4028_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
return v___x_4029_;
}
}
}
}
else
{
lean_dec_ref(v___x_4016_);
lean_dec(v___x_4015_);
lean_dec(v___x_4014_);
lean_dec(v_numNested_4006_);
lean_dec(v_all_4005_);
lean_dec(v_numParams_4004_);
lean_dec(v_indName_3981_);
return v___x_4017_;
}
}
else
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
lean_dec(v_numNested_4006_);
lean_dec(v_all_4005_);
lean_dec(v_numParams_4004_);
lean_dec(v_indName_3981_);
v___x_4040_ = lean_box(0);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4040_);
v___x_4042_ = v___x_4011_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_numNested_4006_);
lean_dec(v_all_4005_);
lean_dec(v_numParams_4004_);
lean_dec(v_indName_3981_);
v_a_4045_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4008_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4008_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4055_; 
lean_dec(v_a_3993_);
lean_dec(v_indName_3981_);
v___x_4053_ = lean_box(0);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_4053_);
v___x_4055_ = v___x_3995_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v_indName_3981_);
v_a_4058_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_3992_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_3992_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
else
{
lean_object* v___f_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v_a_4074_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v_a_4089_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v_a_4094_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v_a_4099_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v_a_4111_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v_a_4116_; 
lean_inc(v_indName_3981_);
v___f_4066_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4066_, 0, v_indName_3981_);
v___x_4067_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4068_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4069_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3989_, v_options_3988_, v___x_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4185_; uint8_t v___x_4186_; 
v___x_4185_ = l_Lean_trace_profiler;
v___x_4186_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3988_, v___x_4185_);
if (v___x_4186_ == 0)
{
lean_object* v___x_4187_; 
lean_dec_ref(v___f_4066_);
lean_inc(v_indName_3981_);
v___x_4187_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4252_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4252_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4252_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
if (lean_obj_tag(v_a_4188_) == 5)
{
lean_object* v_val_4192_; uint8_t v_isRec_4193_; 
v_val_4192_ = lean_ctor_get(v_a_4188_, 0);
lean_inc_ref(v_val_4192_);
lean_dec_ref_known(v_a_4188_, 1);
v_isRec_4193_ = lean_ctor_get_uint8(v_val_4192_, sizeof(void*)*6);
if (v_isRec_4193_ == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
lean_dec_ref(v_val_4192_);
lean_dec(v_indName_3981_);
v___x_4194_ = lean_box(0);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4194_);
v___x_4196_ = v___x_4190_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
else
{
lean_object* v_toConstantVal_4198_; lean_object* v_numParams_4199_; lean_object* v_all_4200_; lean_object* v_numNested_4201_; lean_object* v_type_4202_; lean_object* v___x_4203_; 
lean_del_object(v___x_4190_);
v_toConstantVal_4198_ = lean_ctor_get(v_val_4192_, 0);
lean_inc_ref(v_toConstantVal_4198_);
v_numParams_4199_ = lean_ctor_get(v_val_4192_, 1);
lean_inc(v_numParams_4199_);
v_all_4200_ = lean_ctor_get(v_val_4192_, 3);
lean_inc(v_all_4200_);
v_numNested_4201_ = lean_ctor_get(v_val_4192_, 5);
lean_inc(v_numNested_4201_);
lean_dec_ref(v_val_4192_);
v_type_4202_ = lean_ctor_get(v_toConstantVal_4198_, 2);
lean_inc_ref(v_type_4202_);
lean_dec_ref(v_toConstantVal_4198_);
v___x_4203_ = l_Lean_Meta_isPropFormerType(v_type_4202_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4239_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4206_ = v___x_4203_;
v_isShared_4207_ = v_isSharedCheck_4239_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4203_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4239_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
uint8_t v___x_4208_; 
v___x_4208_ = lean_unbox(v_a_4204_);
lean_dec(v_a_4204_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_del_object(v___x_4206_);
lean_inc_n(v_indName_3981_, 2);
v___x_4209_ = l_Lean_mkRecName(v_indName_3981_);
v___x_4210_ = l_Lean_mkBRecOnName(v_indName_3981_);
lean_inc(v_all_4200_);
v___x_4211_ = lean_array_mk(v_all_4200_);
lean_inc(v___x_4210_);
lean_inc_ref(v___x_4211_);
lean_inc(v_numParams_4199_);
lean_inc(v___x_4209_);
v___x_4212_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4209_, v_numParams_4199_, v___x_4211_, v___x_4210_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4233_; 
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4233_ == 0)
{
lean_object* v_unused_4234_; 
v_unused_4234_ = lean_ctor_get(v___x_4212_, 0);
lean_dec(v_unused_4234_);
v___x_4214_ = v___x_4212_;
v_isShared_4215_ = v_isSharedCheck_4233_;
goto v_resetjp_4213_;
}
else
{
lean_dec(v___x_4212_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4233_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = l_List_get_x21Internal___redArg(v___x_3991_, v_all_4200_, v___x_4216_);
lean_dec(v_all_4200_);
v___x_4218_ = lean_name_eq(v___x_4217_, v_indName_3981_);
lean_dec(v_indName_3981_);
lean_dec(v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; lean_object* v___x_4221_; 
lean_dec_ref(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
lean_dec(v_numNested_4201_);
lean_dec(v_numParams_4199_);
v___x_4219_ = lean_box(0);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4219_);
v___x_4221_ = v___x_4214_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v___x_4219_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_del_object(v___x_4214_);
v___x_4223_ = lean_box(0);
v___x_4224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4201_, v___x_4209_, v___x_4210_, v_numParams_4199_, v___x_4211_, v___x_4216_, v___x_4223_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_numNested_4201_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4231_ == 0)
{
lean_object* v_unused_4232_; 
v_unused_4232_ = lean_ctor_get(v___x_4224_, 0);
lean_dec(v_unused_4232_);
v___x_4226_ = v___x_4224_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_dec(v___x_4224_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4223_);
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v___x_4223_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
else
{
return v___x_4224_;
}
}
}
}
else
{
lean_dec_ref(v___x_4211_);
lean_dec(v___x_4210_);
lean_dec(v___x_4209_);
lean_dec(v_numNested_4201_);
lean_dec(v_all_4200_);
lean_dec(v_numParams_4199_);
lean_dec(v_indName_3981_);
return v___x_4212_;
}
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
lean_dec(v_numNested_4201_);
lean_dec(v_all_4200_);
lean_dec(v_numParams_4199_);
lean_dec(v_indName_3981_);
v___x_4235_ = lean_box(0);
if (v_isShared_4207_ == 0)
{
lean_ctor_set(v___x_4206_, 0, v___x_4235_);
v___x_4237_ = v___x_4206_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_numNested_4201_);
lean_dec(v_all_4200_);
lean_dec(v_numParams_4199_);
lean_dec(v_indName_3981_);
v_a_4240_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4203_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4203_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
lean_dec(v_a_4188_);
lean_dec(v_indName_3981_);
v___x_4248_ = lean_box(0);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4248_);
v___x_4250_ = v___x_4190_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v_indName_3981_);
v_a_4253_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4187_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4187_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
goto v___jp_4118_;
}
}
else
{
goto v___jp_4118_;
}
v___jp_4071_:
{
lean_object* v___x_4075_; double v___x_4076_; double v___x_4077_; double v___x_4078_; double v___x_4079_; double v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4075_ = lean_io_mono_nanos_now();
v___x_4076_ = lean_float_of_nat(v___y_4072_);
v___x_4077_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4078_ = lean_float_div(v___x_4076_, v___x_4077_);
v___x_4079_ = lean_float_of_nat(v___x_4075_);
v___x_4080_ = lean_float_div(v___x_4079_, v___x_4077_);
v___x_4081_ = lean_box_float(v___x_4078_);
v___x_4082_ = lean_box_float(v___x_4080_);
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4084_, 0, v_a_4074_);
lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4067_, v_hasTrace_3990_, v___x_4068_, v_options_3988_, v___x_4070_, v___y_4073_, v___f_4066_, v___x_4084_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
return v___x_4085_;
}
v___jp_4086_:
{
lean_object* v___x_4090_; 
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v_a_4089_);
v___y_4072_ = v___y_4087_;
v___y_4073_ = v___y_4088_;
v_a_4074_ = v___x_4090_;
goto v___jp_4071_;
}
v___jp_4091_:
{
lean_object* v___x_4095_; 
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_a_4094_);
v___y_4072_ = v___y_4092_;
v___y_4073_ = v___y_4093_;
v_a_4074_ = v___x_4095_;
goto v___jp_4071_;
}
v___jp_4096_:
{
lean_object* v___x_4100_; double v___x_4101_; double v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4100_ = lean_io_get_num_heartbeats();
v___x_4101_ = lean_float_of_nat(v___y_4097_);
v___x_4102_ = lean_float_of_nat(v___x_4100_);
v___x_4103_ = lean_box_float(v___x_4101_);
v___x_4104_ = lean_box_float(v___x_4102_);
v___x_4105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4103_);
lean_ctor_set(v___x_4105_, 1, v___x_4104_);
v___x_4106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4106_, 0, v_a_4099_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4067_, v_hasTrace_3990_, v___x_4068_, v_options_3988_, v___x_4070_, v___y_4098_, v___f_4066_, v___x_4106_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
return v___x_4107_;
}
v___jp_4108_:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_a_4111_);
v___y_4097_ = v___y_4109_;
v___y_4098_ = v___y_4110_;
v_a_4099_ = v___x_4112_;
goto v___jp_4096_;
}
v___jp_4113_:
{
lean_object* v___x_4117_; 
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v_a_4116_);
v___y_4097_ = v___y_4114_;
v___y_4098_ = v___y_4115_;
v_a_4099_ = v___x_4117_;
goto v___jp_4096_;
}
v___jp_4118_:
{
lean_object* v___x_4119_; lean_object* v_a_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v___x_4119_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3985_);
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
v___x_4121_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4122_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3988_, v___x_4121_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3981_);
v___x_4124_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
if (lean_obj_tag(v_a_4125_) == 5)
{
lean_object* v_val_4126_; uint8_t v_isRec_4127_; 
v_val_4126_ = lean_ctor_get(v_a_4125_, 0);
lean_inc_ref(v_val_4126_);
lean_dec_ref_known(v_a_4125_, 1);
v_isRec_4127_ = lean_ctor_get_uint8(v_val_4126_, sizeof(void*)*6);
if (v_isRec_4127_ == 0)
{
lean_object* v___x_4128_; 
lean_dec_ref(v_val_4126_);
lean_dec(v_indName_3981_);
v___x_4128_ = lean_box(0);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v___x_4128_;
goto v___jp_4086_;
}
else
{
lean_object* v_toConstantVal_4129_; lean_object* v_numParams_4130_; lean_object* v_all_4131_; lean_object* v_numNested_4132_; lean_object* v_type_4133_; lean_object* v___x_4134_; 
v_toConstantVal_4129_ = lean_ctor_get(v_val_4126_, 0);
lean_inc_ref(v_toConstantVal_4129_);
v_numParams_4130_ = lean_ctor_get(v_val_4126_, 1);
lean_inc(v_numParams_4130_);
v_all_4131_ = lean_ctor_get(v_val_4126_, 3);
lean_inc(v_all_4131_);
v_numNested_4132_ = lean_ctor_get(v_val_4126_, 5);
lean_inc(v_numNested_4132_);
lean_dec_ref(v_val_4126_);
v_type_4133_ = lean_ctor_get(v_toConstantVal_4129_, 2);
lean_inc_ref(v_type_4133_);
lean_dec_ref(v_toConstantVal_4129_);
v___x_4134_ = l_Lean_Meta_isPropFormerType(v_type_4133_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; uint8_t v___x_4136_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___x_4136_ = lean_unbox(v_a_4135_);
lean_dec(v_a_4135_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_inc_n(v_indName_3981_, 2);
v___x_4137_ = l_Lean_mkRecName(v_indName_3981_);
v___x_4138_ = l_Lean_mkBRecOnName(v_indName_3981_);
lean_inc(v_all_4131_);
v___x_4139_ = lean_array_mk(v_all_4131_);
lean_inc(v___x_4138_);
lean_inc_ref(v___x_4139_);
lean_inc(v_numParams_4130_);
lean_inc(v___x_4137_);
v___x_4140_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4137_, v_numParams_4130_, v___x_4139_, v___x_4138_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
lean_dec_ref_known(v___x_4140_, 1);
v___x_4141_ = lean_unsigned_to_nat(0u);
v___x_4142_ = l_List_get_x21Internal___redArg(v___x_3991_, v_all_4131_, v___x_4141_);
lean_dec(v_all_4131_);
v___x_4143_ = lean_name_eq(v___x_4142_, v_indName_3981_);
lean_dec(v_indName_3981_);
lean_dec(v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; 
lean_dec_ref(v___x_4139_);
lean_dec(v___x_4138_);
lean_dec(v___x_4137_);
lean_dec(v_numNested_4132_);
lean_dec(v_numParams_4130_);
v___x_4144_ = lean_box(0);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v___x_4144_;
goto v___jp_4086_;
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_box(0);
v___x_4146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4132_, v___x_4137_, v___x_4138_, v_numParams_4130_, v___x_4139_, v___x_4141_, v___x_4145_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_numNested_4132_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_dec_ref_known(v___x_4146_, 1);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v___x_4145_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4147_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
v___y_4092_ = v___x_4123_;
v___y_4093_ = v_a_4120_;
v_a_4094_ = v_a_4147_;
goto v___jp_4091_;
}
}
}
else
{
lean_dec_ref(v___x_4139_);
lean_dec(v___x_4138_);
lean_dec(v___x_4137_);
lean_dec(v_numNested_4132_);
lean_dec(v_all_4131_);
lean_dec(v_numParams_4130_);
lean_dec(v_indName_3981_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4148_; 
v_a_4148_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v_a_4148_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4149_; 
v_a_4149_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4092_ = v___x_4123_;
v___y_4093_ = v_a_4120_;
v_a_4094_ = v_a_4149_;
goto v___jp_4091_;
}
}
}
else
{
lean_object* v___x_4150_; 
lean_dec(v_numNested_4132_);
lean_dec(v_all_4131_);
lean_dec(v_numParams_4130_);
lean_dec(v_indName_3981_);
v___x_4150_ = lean_box(0);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v___x_4150_;
goto v___jp_4086_;
}
}
else
{
lean_object* v_a_4151_; 
lean_dec(v_numNested_4132_);
lean_dec(v_all_4131_);
lean_dec(v_numParams_4130_);
lean_dec(v_indName_3981_);
v_a_4151_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4092_ = v___x_4123_;
v___y_4093_ = v_a_4120_;
v_a_4094_ = v_a_4151_;
goto v___jp_4091_;
}
}
}
else
{
lean_object* v___x_4152_; 
lean_dec(v_a_4125_);
lean_dec(v_indName_3981_);
v___x_4152_ = lean_box(0);
v___y_4087_ = v___x_4123_;
v___y_4088_ = v_a_4120_;
v_a_4089_ = v___x_4152_;
goto v___jp_4086_;
}
}
else
{
lean_object* v_a_4153_; 
lean_dec(v_indName_3981_);
v_a_4153_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4124_, 1);
v___y_4092_ = v___x_4123_;
v___y_4093_ = v_a_4120_;
v_a_4094_ = v_a_4153_;
goto v___jp_4091_;
}
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3981_);
v___x_4155_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
if (lean_obj_tag(v_a_4156_) == 5)
{
lean_object* v_val_4157_; uint8_t v_isRec_4158_; 
v_val_4157_ = lean_ctor_get(v_a_4156_, 0);
lean_inc_ref(v_val_4157_);
lean_dec_ref_known(v_a_4156_, 1);
v_isRec_4158_ = lean_ctor_get_uint8(v_val_4157_, sizeof(void*)*6);
if (v_isRec_4158_ == 0)
{
lean_object* v___x_4159_; 
lean_dec_ref(v_val_4157_);
lean_dec(v_indName_3981_);
v___x_4159_ = lean_box(0);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v___x_4159_;
goto v___jp_4108_;
}
else
{
lean_object* v_toConstantVal_4160_; lean_object* v_numParams_4161_; lean_object* v_all_4162_; lean_object* v_numNested_4163_; lean_object* v_type_4164_; lean_object* v___x_4165_; 
v_toConstantVal_4160_ = lean_ctor_get(v_val_4157_, 0);
lean_inc_ref(v_toConstantVal_4160_);
v_numParams_4161_ = lean_ctor_get(v_val_4157_, 1);
lean_inc(v_numParams_4161_);
v_all_4162_ = lean_ctor_get(v_val_4157_, 3);
lean_inc(v_all_4162_);
v_numNested_4163_ = lean_ctor_get(v_val_4157_, 5);
lean_inc(v_numNested_4163_);
lean_dec_ref(v_val_4157_);
v_type_4164_ = lean_ctor_get(v_toConstantVal_4160_, 2);
lean_inc_ref(v_type_4164_);
lean_dec_ref(v_toConstantVal_4160_);
v___x_4165_ = l_Lean_Meta_isPropFormerType(v_type_4164_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; uint8_t v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = lean_unbox(v_a_4166_);
lean_dec(v_a_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
lean_inc_n(v_indName_3981_, 2);
v___x_4168_ = l_Lean_mkRecName(v_indName_3981_);
v___x_4169_ = l_Lean_mkBRecOnName(v_indName_3981_);
lean_inc(v_all_4162_);
v___x_4170_ = lean_array_mk(v_all_4162_);
lean_inc(v___x_4169_);
lean_inc_ref(v___x_4170_);
lean_inc(v_numParams_4161_);
lean_inc(v___x_4168_);
v___x_4171_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4168_, v_numParams_4161_, v___x_4170_, v___x_4169_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; 
lean_dec_ref_known(v___x_4171_, 1);
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = l_List_get_x21Internal___redArg(v___x_3991_, v_all_4162_, v___x_4172_);
lean_dec(v_all_4162_);
v___x_4174_ = lean_name_eq(v___x_4173_, v_indName_3981_);
lean_dec(v_indName_3981_);
lean_dec(v___x_4173_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; 
lean_dec_ref(v___x_4170_);
lean_dec(v___x_4169_);
lean_dec(v___x_4168_);
lean_dec(v_numNested_4163_);
lean_dec(v_numParams_4161_);
v___x_4175_ = lean_box(0);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v___x_4175_;
goto v___jp_4108_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4176_ = lean_box(0);
v___x_4177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4163_, v___x_4168_, v___x_4169_, v_numParams_4161_, v___x_4170_, v___x_4172_, v___x_4176_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_numNested_4163_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_dec_ref_known(v___x_4177_, 1);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v___x_4176_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4178_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v___y_4114_ = v___x_4154_;
v___y_4115_ = v_a_4120_;
v_a_4116_ = v_a_4178_;
goto v___jp_4113_;
}
}
}
else
{
lean_dec_ref(v___x_4170_);
lean_dec(v___x_4169_);
lean_dec(v___x_4168_);
lean_dec(v_numNested_4163_);
lean_dec(v_all_4162_);
lean_dec(v_numParams_4161_);
lean_dec(v_indName_3981_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4179_; 
v_a_4179_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4171_, 1);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v_a_4179_;
goto v___jp_4108_;
}
else
{
lean_object* v_a_4180_; 
v_a_4180_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4171_, 1);
v___y_4114_ = v___x_4154_;
v___y_4115_ = v_a_4120_;
v_a_4116_ = v_a_4180_;
goto v___jp_4113_;
}
}
}
else
{
lean_object* v___x_4181_; 
lean_dec(v_numNested_4163_);
lean_dec(v_all_4162_);
lean_dec(v_numParams_4161_);
lean_dec(v_indName_3981_);
v___x_4181_ = lean_box(0);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v___x_4181_;
goto v___jp_4108_;
}
}
else
{
lean_object* v_a_4182_; 
lean_dec(v_numNested_4163_);
lean_dec(v_all_4162_);
lean_dec(v_numParams_4161_);
lean_dec(v_indName_3981_);
v_a_4182_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4165_, 1);
v___y_4114_ = v___x_4154_;
v___y_4115_ = v_a_4120_;
v_a_4116_ = v_a_4182_;
goto v___jp_4113_;
}
}
}
else
{
lean_object* v___x_4183_; 
lean_dec(v_a_4156_);
lean_dec(v_indName_3981_);
v___x_4183_ = lean_box(0);
v___y_4109_ = v___x_4154_;
v___y_4110_ = v_a_4120_;
v_a_4111_ = v___x_4183_;
goto v___jp_4108_;
}
}
else
{
lean_object* v_a_4184_; 
lean_dec(v_indName_3981_);
v_a_4184_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4155_, 1);
v___y_4114_ = v___x_4154_;
v___y_4115_ = v_a_4120_;
v_a_4116_ = v_a_4184_;
goto v___jp_4113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_mkBRecOn(v_indName_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4268_, lean_object* v___x_4269_, lean_object* v___x_4270_, lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v_inst_4273_, lean_object* v_R_4274_, lean_object* v_a_4275_, lean_object* v_b_4276_, lean_object* v_c_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4268_, v___x_4269_, v___x_4270_, v___x_4271_, v___x_4272_, v_a_4275_, v_b_4276_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v_inst_4289_, lean_object* v_R_4290_, lean_object* v_a_4291_, lean_object* v_b_4292_, lean_object* v_c_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4284_, v___x_4285_, v___x_4286_, v___x_4287_, v___x_4288_, v_inst_4289_, v_R_4290_, v_a_4291_, v_b_4292_, v_c_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec(v_upperBound_4284_);
return v_res_4299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4345_ = lean_unsigned_to_nat(2304625798u);
v___x_4346_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4347_ = l_Lean_Name_num___override(v___x_4346_, v___x_4345_);
return v___x_4347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4350_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4351_ = l_Lean_Name_str___override(v___x_4350_, v___x_4349_);
return v___x_4351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4354_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4355_ = l_Lean_Name_str___override(v___x_4354_, v___x_4353_);
return v___x_4355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = lean_unsigned_to_nat(2u);
v___x_4357_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4358_ = l_Lean_Name_num___override(v___x_4357_, v___x_4356_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4360_; uint8_t v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4360_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4361_ = 0;
v___x_4362_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4363_ = l_Lean_registerTraceClass(v___x_4360_, v___x_4361_, v___x_4362_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4365_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_BRecOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_BRecOn(builtin);
}
#ifdef __cplusplus
}
#endif
