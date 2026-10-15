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
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26;
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
uint8_t v___x_9138__boxed_555_; lean_object* v_res_556_; 
v___x_9138__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9138__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__21));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__23));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__25));
v___x_974_ = l_Lean_stringToMessageData(v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_975_, lean_object* v_declHint_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_env_981_; uint8_t v___x_982_; 
v___x_979_ = lean_box(0);
v___x_980_ = lean_st_ref_get(v___y_977_);
v_env_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_980_);
v___x_982_ = l_Lean_Name_isAnonymous(v_declHint_976_);
if (v___x_982_ == 0)
{
uint8_t v_isExporting_983_; 
v_isExporting_983_ = lean_ctor_get_uint8(v_env_981_, sizeof(void*)*13);
if (v_isExporting_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v_env_981_);
lean_dec(v_declHint_976_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_msg_975_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; uint8_t v___x_986_; 
lean_inc_ref(v_env_981_);
v___x_985_ = l_Lean_Environment_setExporting(v_env_981_, v___x_982_);
lean_inc(v_declHint_976_);
lean_inc_ref(v___x_985_);
v___x_986_ = l_Lean_Environment_contains(v___x_985_, v_declHint_976_, v_isExporting_983_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v___x_985_);
lean_dec_ref(v_env_981_);
lean_dec(v_declHint_976_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_msg_975_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_c_993_; lean_object* v___x_994_; 
v___x_988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_989_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_990_ = l_Lean_Options_empty;
v___x_991_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_991_, 0, v___x_985_);
lean_ctor_set(v___x_991_, 1, v___x_988_);
lean_ctor_set(v___x_991_, 2, v___x_989_);
lean_ctor_set(v___x_991_, 3, v___x_990_);
lean_inc(v_declHint_976_);
v___x_992_ = l_Lean_MessageData_ofConstName(v_declHint_976_, v___x_982_);
v_c_993_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_993_, 0, v___x_991_);
lean_ctor_set(v_c_993_, 1, v___x_992_);
v___x_994_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_981_, v_declHint_976_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec_ref(v_env_981_);
lean_dec(v_declHint_976_);
v___x_995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_c_993_);
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_MessageData_note(v___x_998_);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_msg_975_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
else
{
lean_object* v_val_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1058_; 
v_val_1002_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1004_ = v___x_994_;
v_isShared_1005_ = v_isSharedCheck_1058_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_val_1002_);
lean_dec(v___x_994_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1058_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_modules_1007_; lean_object* v_moduleNames_1008_; lean_object* v_mod_1009_; uint8_t v___y_1011_; uint8_t v___x_1041_; 
v___x_1006_ = l_Lean_Environment_header(v_env_981_);
lean_dec_ref(v_env_981_);
v_modules_1007_ = lean_ctor_get(v___x_1006_, 3);
lean_inc_ref(v_modules_1007_);
v_moduleNames_1008_ = lean_ctor_get(v___x_1006_, 4);
lean_inc_ref(v_moduleNames_1008_);
lean_dec_ref(v___x_1006_);
v_mod_1009_ = lean_array_get(v___x_979_, v_moduleNames_1008_, v_val_1002_);
lean_dec_ref(v_moduleNames_1008_);
v___x_1041_ = l_Lean_isPrivateName(v_declHint_976_);
lean_dec(v_declHint_976_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_array_get_size(v_modules_1007_);
v___x_1043_ = lean_nat_dec_lt(v_val_1002_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec_ref(v_modules_1007_);
lean_dec(v_val_1002_);
v___y_1011_ = v___x_1041_;
goto v___jp_1010_;
}
else
{
lean_object* v___x_1044_; lean_object* v_toImport_1045_; uint8_t v_isExported_1046_; 
v___x_1044_ = lean_array_fget(v_modules_1007_, v_val_1002_);
lean_dec(v_val_1002_);
lean_dec_ref(v_modules_1007_);
v_toImport_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc_ref(v_toImport_1045_);
lean_dec(v___x_1044_);
v_isExported_1046_ = lean_ctor_get_uint8(v_toImport_1045_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1045_);
v___y_1011_ = v_isExported_1046_;
goto v___jp_1010_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v_modules_1007_);
lean_del_object(v___x_1004_);
lean_dec(v_val_1002_);
v___x_1047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v_c_993_);
v___x_1049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Lean_MessageData_ofName(v_mod_1009_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_MessageData_note(v___x_1054_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_msg_975_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
v___jp_1010_:
{
if (v___y_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_c_993_);
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofName(v_mod_1009_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_note(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_msg_975_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set_tag(v___x_1004_, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1021_);
v___x_1023_ = v___x_1004_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_c_993_);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_ofName(v_mod_1009_);
lean_inc_ref(v___x_1029_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_1029_);
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_MessageData_note(v___x_1035_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_msg_975_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set_tag(v___x_1004_, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1037_);
v___x_1039_ = v___x_1004_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
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
}
}
}
}
else
{
lean_object* v___x_1059_; 
lean_dec_ref(v_env_981_);
lean_dec(v_declHint_976_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_msg_975_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1060_, lean_object* v_declHint_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1060_, v_declHint_1061_, v___y_1062_);
lean_dec(v___y_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1065_, lean_object* v_declHint_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
v___x_1072_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1065_, v_declHint_1066_, v___y_1070_);
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = l_Lean_unknownIdentifierMessageTag;
v___x_1078_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_a_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1083_, v_declHint_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1091_, lean_object* v_msg_1092_, lean_object* v_declHint_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v_a_1100_; lean_object* v___x_1101_; 
v___x_1099_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1092_, v_declHint_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1091_, v_a_1100_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1102_, lean_object* v_msg_1103_, lean_object* v_declHint_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1102_, v_msg_1103_, v_declHint_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v_ref_1102_);
return v_res_1110_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1117_, lean_object* v_constName_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1125_ = 0;
lean_inc(v_constName_1118_);
v___x_1126_ = l_Lean_MessageData_ofConstName(v_constName_1118_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1117_, v___x_1129_, v_constName_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1131_, lean_object* v_constName_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1131_, v_constName_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v_ref_1131_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_ref_1145_; lean_object* v___x_1146_; 
v_ref_1145_ = lean_ctor_get(v___y_1142_, 2);
v___x_1146_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1145_, v_constName_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v_env_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1160_ = lean_st_ref_get(v___y_1158_);
v_env_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc_ref(v_env_1161_);
lean_dec(v___x_1160_);
v___x_1162_ = 0;
lean_inc(v_constName_1154_);
v___x_1163_ = l_Lean_Environment_find_x3f(v_env_1161_, v_constName_1154_, v___x_1162_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
return v___x_1164_;
}
else
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_constName_1154_);
v_val_1165_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1163_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_val_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
return v_res_1179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1182_ = l_Lean_stringToMessageData(v___x_1181_);
return v___x_1182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1185_ = l_Lean_stringToMessageData(v___x_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1189_, lean_object* v_nParams_1190_, lean_object* v_belowName_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1189_);
v___x_1198_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1189_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
if (lean_obj_tag(v_a_1199_) == 7)
{
lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1317_; 
v_val_1200_ = lean_ctor_get(v_a_1199_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_a_1199_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1202_ = v_a_1199_;
v_isShared_1203_ = v_isSharedCheck_1317_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_dec(v_a_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1317_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_toConstantVal_1204_; lean_object* v_numMotives_1205_; lean_object* v_numMinors_1206_; lean_object* v_levelParams_1207_; lean_object* v_type_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v_toConstantVal_1204_ = lean_ctor_get(v_val_1200_, 0);
lean_inc_ref(v_toConstantVal_1204_);
v_numMotives_1205_ = lean_ctor_get(v_val_1200_, 4);
lean_inc(v_numMotives_1205_);
v_numMinors_1206_ = lean_ctor_get(v_val_1200_, 5);
lean_inc(v_numMinors_1206_);
lean_dec_ref(v_val_1200_);
v_levelParams_1207_ = lean_ctor_get(v_toConstantVal_1204_, 1);
lean_inc_n(v_levelParams_1207_, 2);
v_type_1208_ = lean_ctor_get(v_toConstantVal_1204_, 2);
lean_inc_ref(v_type_1208_);
lean_dec_ref(v_toConstantVal_1204_);
v___x_1209_ = lean_box(0);
v___x_1210_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1207_, v___x_1209_);
if (lean_obj_tag(v___x_1210_) == 1)
{
lean_object* v_head_1211_; lean_object* v_tail_1212_; lean_object* v___f_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; 
v_head_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_head_1211_);
v_tail_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_tail_1212_);
lean_dec_ref_known(v___x_1210_, 2);
v___f_1213_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1213_, 0, v_nParams_1190_);
lean_closure_set(v___f_1213_, 1, v_numMotives_1205_);
lean_closure_set(v___f_1213_, 2, v_numMinors_1206_);
lean_closure_set(v___f_1213_, 3, v___x_1197_);
lean_closure_set(v___f_1213_, 4, v_head_1211_);
lean_closure_set(v___f_1213_, 5, v_tail_1212_);
lean_closure_set(v___f_1213_, 6, v_recName_1189_);
lean_closure_set(v___f_1213_, 7, v_belowName_1191_);
lean_closure_set(v___f_1213_, 8, v_levelParams_1207_);
v___x_1214_ = 0;
v___x_1215_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1208_, v___f_1213_, v___x_1214_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc_n(v_a_1216_, 2);
lean_dec_ref_known(v___x_1215_, 1);
if (v_isShared_1203_ == 0)
{
lean_ctor_set_tag(v___x_1202_, 1);
lean_ctor_set(v___x_1202_, 0, v_a_1216_);
v___x_1218_ = v___x_1202_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1216_);
v___x_1218_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_addDecl(v___x_1218_, v___x_1214_, v_a_1194_, v_a_1195_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_toConstantVal_1220_; lean_object* v_name_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref_known(v___x_1219_, 1);
v_toConstantVal_1220_ = lean_ctor_get(v_a_1216_, 0);
lean_inc_ref(v_toConstantVal_1220_);
lean_dec(v_a_1216_);
v_name_1221_ = lean_ctor_get(v_toConstantVal_1220_, 0);
lean_inc_n(v_name_1221_, 2);
lean_dec_ref(v_toConstantVal_1220_);
v___x_1222_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1221_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1301_);
v___x_1224_ = v___x_1222_;
v_isShared_1225_ = v_isSharedCheck_1300_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1300_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_traceState_1231_; lean_object* v_recordedDeps_1232_; lean_object* v_messages_1233_; lean_object* v_infoState_1234_; lean_object* v_snapshotTasks_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1298_; 
v___x_1226_ = lean_st_ref_take(v_a_1195_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1226_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1226_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1226_, 3);
v_traceState_1231_ = lean_ctor_get(v___x_1226_, 4);
v_recordedDeps_1232_ = lean_ctor_get(v___x_1226_, 6);
v_messages_1233_ = lean_ctor_get(v___x_1226_, 7);
v_infoState_1234_ = lean_ctor_get(v___x_1226_, 8);
v_snapshotTasks_1235_ = lean_ctor_get(v___x_1226_, 9);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v___x_1226_, 5);
lean_dec(v_unused_1299_);
v___x_1237_ = v___x_1226_;
v_isShared_1238_ = v_isSharedCheck_1298_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snapshotTasks_1235_);
lean_inc(v_infoState_1234_);
lean_inc(v_messages_1233_);
lean_inc(v_recordedDeps_1232_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1298_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_inc(v_name_1221_);
v___x_1239_ = l_Lean_markAuxRecursor(v_env_1227_, v_name_1221_);
v___x_1240_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 5, v___x_1240_);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1242_ = v___x_1237_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_traceState_1231_);
lean_ctor_set(v_reuseFailAlloc_1297_, 5, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1297_, 6, v_recordedDeps_1232_);
lean_ctor_set(v_reuseFailAlloc_1297_, 7, v_messages_1233_);
lean_ctor_set(v_reuseFailAlloc_1297_, 8, v_infoState_1234_);
lean_ctor_set(v_reuseFailAlloc_1297_, 9, v_snapshotTasks_1235_);
v___x_1242_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_mctx_1245_; lean_object* v_zetaDeltaFVarIds_1246_; lean_object* v_postponed_1247_; lean_object* v_diag_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1295_; 
v___x_1243_ = lean_st_ref_put(v_a_1195_, v___x_1242_);
v___x_1244_ = lean_st_ref_take(v_a_1193_);
v_mctx_1245_ = lean_ctor_get(v___x_1244_, 0);
v_zetaDeltaFVarIds_1246_ = lean_ctor_get(v___x_1244_, 2);
v_postponed_1247_ = lean_ctor_get(v___x_1244_, 3);
v_diag_1248_ = lean_ctor_get(v___x_1244_, 4);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; 
v_unused_1296_ = lean_ctor_get(v___x_1244_, 1);
lean_dec(v_unused_1296_);
v___x_1250_ = v___x_1244_;
v_isShared_1251_ = v_isSharedCheck_1295_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_diag_1248_);
lean_inc(v_postponed_1247_);
lean_inc(v_zetaDeltaFVarIds_1246_);
lean_inc(v_mctx_1245_);
lean_dec(v___x_1244_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1295_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1252_);
v___x_1254_ = v___x_1250_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_mctx_1245_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_zetaDeltaFVarIds_1246_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_postponed_1247_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_diag_1248_);
v___x_1254_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v_env_1257_; lean_object* v_nextMacroScope_1258_; lean_object* v_ngen_1259_; lean_object* v_auxDeclNGen_1260_; lean_object* v_traceState_1261_; lean_object* v_recordedDeps_1262_; lean_object* v_messages_1263_; lean_object* v_infoState_1264_; lean_object* v_snapshotTasks_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1292_; 
v___x_1255_ = lean_st_ref_put(v_a_1193_, v___x_1254_);
v___x_1256_ = lean_st_ref_take(v_a_1195_);
v_env_1257_ = lean_ctor_get(v___x_1256_, 0);
v_nextMacroScope_1258_ = lean_ctor_get(v___x_1256_, 1);
v_ngen_1259_ = lean_ctor_get(v___x_1256_, 2);
v_auxDeclNGen_1260_ = lean_ctor_get(v___x_1256_, 3);
v_traceState_1261_ = lean_ctor_get(v___x_1256_, 4);
v_recordedDeps_1262_ = lean_ctor_get(v___x_1256_, 6);
v_messages_1263_ = lean_ctor_get(v___x_1256_, 7);
v_infoState_1264_ = lean_ctor_get(v___x_1256_, 8);
v_snapshotTasks_1265_ = lean_ctor_get(v___x_1256_, 9);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1256_, 5);
lean_dec(v_unused_1293_);
v___x_1267_ = v___x_1256_;
v_isShared_1268_ = v_isSharedCheck_1292_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snapshotTasks_1265_);
lean_inc(v_infoState_1264_);
lean_inc(v_messages_1263_);
lean_inc(v_recordedDeps_1262_);
lean_inc(v_traceState_1261_);
lean_inc(v_auxDeclNGen_1260_);
lean_inc(v_ngen_1259_);
lean_inc(v_nextMacroScope_1258_);
lean_inc(v_env_1257_);
lean_dec(v___x_1256_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1292_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1269_ = l_Lean_addProtected(v_env_1257_, v_name_1221_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 5, v___x_1240_);
lean_ctor_set(v___x_1267_, 0, v___x_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_nextMacroScope_1258_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_ngen_1259_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_auxDeclNGen_1260_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_traceState_1261_);
lean_ctor_set(v_reuseFailAlloc_1291_, 5, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1291_, 6, v_recordedDeps_1262_);
lean_ctor_set(v_reuseFailAlloc_1291_, 7, v_messages_1263_);
lean_ctor_set(v_reuseFailAlloc_1291_, 8, v_infoState_1264_);
lean_ctor_set(v_reuseFailAlloc_1291_, 9, v_snapshotTasks_1265_);
v___x_1271_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_mctx_1274_; lean_object* v_zetaDeltaFVarIds_1275_; lean_object* v_postponed_1276_; lean_object* v_diag_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1289_; 
v___x_1272_ = lean_st_ref_put(v_a_1195_, v___x_1271_);
v___x_1273_ = lean_st_ref_take(v_a_1193_);
v_mctx_1274_ = lean_ctor_get(v___x_1273_, 0);
v_zetaDeltaFVarIds_1275_ = lean_ctor_get(v___x_1273_, 2);
v_postponed_1276_ = lean_ctor_get(v___x_1273_, 3);
v_diag_1277_ = lean_ctor_get(v___x_1273_, 4);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v___x_1273_, 1);
lean_dec(v_unused_1290_);
v___x_1279_ = v___x_1273_;
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_diag_1277_);
lean_inc(v_postponed_1276_);
lean_inc(v_zetaDeltaFVarIds_1275_);
lean_inc(v_mctx_1274_);
lean_dec(v___x_1273_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1289_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1252_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_mctx_1274_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v_zetaDeltaFVarIds_1275_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_postponed_1276_);
lean_ctor_set(v_reuseFailAlloc_1288_, 4, v_diag_1277_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1284_ = lean_st_ref_put(v_a_1193_, v___x_1283_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1281_);
v___x_1286_ = v___x_1224_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
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
lean_dec(v_a_1216_);
return v___x_1219_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_del_object(v___x_1202_);
v_a_1303_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1215_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1215_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec(v___x_1210_);
lean_dec_ref(v_type_1208_);
lean_dec(v_levelParams_1207_);
lean_dec(v_numMinors_1206_);
lean_dec(v_numMotives_1205_);
lean_del_object(v___x_1202_);
lean_dec(v_belowName_1191_);
lean_dec(v_nParams_1190_);
v___x_1311_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1312_ = l_Lean_MessageData_ofName(v_recName_1189_);
v___x_1313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1313_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1315_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1316_;
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec(v_a_1199_);
lean_dec(v_belowName_1191_);
lean_dec(v_nParams_1190_);
v___x_1318_ = l_Lean_MessageData_ofName(v_recName_1189_);
v___x_1319_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1320_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1321_;
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_belowName_1191_);
lean_dec(v_nParams_1190_);
lean_dec(v_recName_1189_);
v_a_1322_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1198_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1198_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1330_, lean_object* v_nParams_1331_, lean_object* v_belowName_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1330_, v_nParams_1331_, v_belowName_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1339_, lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_msg_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1347_, v_msg_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1355_, uint8_t v_s_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1355_, v_s_1356_, v___y_1358_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1363_, lean_object* v_s_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_s_boxed_1370_; lean_object* v_res_1371_; 
v_s_boxed_1370_ = lean_unbox(v_s_1364_);
v_res_1371_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1363_, v_s_boxed_1370_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1372_, lean_object* v_constName_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1380_, v_constName_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_constName_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1389_, v_constName_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1397_, lean_object* v_ref_1398_, lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1397_, v_ref_1398_, v_constName_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_ref_1398_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1406_, lean_object* v_ref_1407_, lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1407_, v_msg_1408_, v_declHint_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ref_1417_, lean_object* v_msg_1418_, lean_object* v_declHint_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1416_, v_ref_1417_, v_msg_1418_, v_declHint_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v_ref_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1426_, lean_object* v_declHint_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1426_, v_declHint_1427_, v___y_1431_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1434_, lean_object* v_declHint_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1434_, v_declHint_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1442_, lean_object* v_ref_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1443_, v_msg_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_ref_1452_, lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1451_, v_ref_1452_, v_msg_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_ref_1452_);
return v_res_1459_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_unsigned_to_nat(32u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
return v___x_1462_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1463_ = ((size_t)5ULL);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_unsigned_to_nat(32u);
v___x_1466_ = lean_mk_empty_array_with_capacity(v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1468_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
lean_ctor_set(v___x_1468_, 2, v___x_1464_);
lean_ctor_set(v___x_1468_, 3, v___x_1464_);
lean_ctor_set_usize(v___x_1468_, 4, v___x_1463_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v_traceState_1472_; lean_object* v_traces_1473_; lean_object* v___x_1474_; lean_object* v_traceState_1475_; lean_object* v_env_1476_; lean_object* v_nextMacroScope_1477_; lean_object* v_ngen_1478_; lean_object* v_auxDeclNGen_1479_; lean_object* v_cache_1480_; lean_object* v_recordedDeps_1481_; lean_object* v_messages_1482_; lean_object* v_infoState_1483_; lean_object* v_snapshotTasks_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1503_; 
v___x_1471_ = lean_st_ref_get(v___y_1469_);
v_traceState_1472_ = lean_ctor_get(v___x_1471_, 4);
lean_inc_ref(v_traceState_1472_);
lean_dec(v___x_1471_);
v_traces_1473_ = lean_ctor_get(v_traceState_1472_, 0);
lean_inc_ref(v_traces_1473_);
lean_dec_ref(v_traceState_1472_);
v___x_1474_ = lean_st_ref_take(v___y_1469_);
v_traceState_1475_ = lean_ctor_get(v___x_1474_, 4);
v_env_1476_ = lean_ctor_get(v___x_1474_, 0);
v_nextMacroScope_1477_ = lean_ctor_get(v___x_1474_, 1);
v_ngen_1478_ = lean_ctor_get(v___x_1474_, 2);
v_auxDeclNGen_1479_ = lean_ctor_get(v___x_1474_, 3);
v_cache_1480_ = lean_ctor_get(v___x_1474_, 5);
v_recordedDeps_1481_ = lean_ctor_get(v___x_1474_, 6);
v_messages_1482_ = lean_ctor_get(v___x_1474_, 7);
v_infoState_1483_ = lean_ctor_get(v___x_1474_, 8);
v_snapshotTasks_1484_ = lean_ctor_get(v___x_1474_, 9);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1486_ = v___x_1474_;
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snapshotTasks_1484_);
lean_inc(v_infoState_1483_);
lean_inc(v_messages_1482_);
lean_inc(v_recordedDeps_1481_);
lean_inc(v_cache_1480_);
lean_inc(v_traceState_1475_);
lean_inc(v_auxDeclNGen_1479_);
lean_inc(v_ngen_1478_);
lean_inc(v_nextMacroScope_1477_);
lean_inc(v_env_1476_);
lean_dec(v___x_1474_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1503_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint64_t v_tid_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1501_; 
v_tid_1488_ = lean_ctor_get_uint64(v_traceState_1475_, sizeof(void*)*1);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_traceState_1475_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_traceState_1475_, 0);
lean_dec(v_unused_1502_);
v___x_1490_ = v_traceState_1475_;
v_isShared_1491_ = v_isSharedCheck_1501_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v_traceState_1475_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1501_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1492_);
lean_ctor_set_uint64(v_reuseFailAlloc_1500_, sizeof(void*)*1, v_tid_1488_);
v___x_1494_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1494_);
v___x_1496_ = v___x_1486_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_env_1476_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_nextMacroScope_1477_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_ngen_1478_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_auxDeclNGen_1479_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1499_, 5, v_cache_1480_);
lean_ctor_set(v_reuseFailAlloc_1499_, 6, v_recordedDeps_1481_);
lean_ctor_set(v_reuseFailAlloc_1499_, 7, v_messages_1482_);
lean_ctor_set(v_reuseFailAlloc_1499_, 8, v_infoState_1483_);
lean_ctor_set(v_reuseFailAlloc_1499_, 9, v_snapshotTasks_1484_);
v___x_1496_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_st_ref_put(v___y_1469_, v___x_1496_);
v___x_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1498_, 0, v_traces_1473_);
return v___x_1498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1504_);
lean_dec(v___y_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1519_, lean_object* v_opt_1520_){
_start:
{
lean_object* v_name_1521_; lean_object* v_defValue_1522_; lean_object* v_map_1523_; lean_object* v___x_1524_; 
v_name_1521_ = lean_ctor_get(v_opt_1520_, 0);
v_defValue_1522_ = lean_ctor_get(v_opt_1520_, 1);
v_map_1523_ = lean_ctor_get(v_opts_1519_, 0);
v___x_1524_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1523_, v_name_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
uint8_t v___x_1525_; 
v___x_1525_ = lean_unbox(v_defValue_1522_);
return v___x_1525_;
}
else
{
lean_object* v_val_1526_; 
v_val_1526_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1526_);
lean_dec_ref_known(v___x_1524_, 1);
if (lean_obj_tag(v_val_1526_) == 1)
{
uint8_t v_v_1527_; 
v_v_1527_ = lean_ctor_get_uint8(v_val_1526_, 0);
lean_dec_ref_known(v_val_1526_, 0);
return v_v_1527_;
}
else
{
uint8_t v___x_1528_; 
lean_dec(v_val_1526_);
v___x_1528_ = lean_unbox(v_defValue_1522_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1529_, lean_object* v_opt_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1529_, v_opt_1530_);
lean_dec_ref(v_opt_1530_);
lean_dec_ref(v_opts_1529_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1533_, lean_object* v_x_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = l_Lean_MessageData_ofName(v_indName_1533_);
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1542_, lean_object* v_x_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_mkBelow___lam__0(v_indName_1542_, v_x_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_x_1543_);
return v_res_1549_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1550_){
_start:
{
if (lean_obj_tag(v_e_1550_) == 0)
{
uint8_t v___x_1551_; 
v___x_1551_ = 2;
return v___x_1551_;
}
else
{
uint8_t v___x_1552_; 
v___x_1552_ = 0;
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1553_);
lean_dec_ref(v_e_1553_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1556_){
_start:
{
if (lean_obj_tag(v_x_1556_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
v_a_1558_ = lean_ctor_get(v_x_1556_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1556_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v_x_1556_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v_x_1556_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 1);
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
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
v_a_1566_ = lean_ctor_get(v_x_1556_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_x_1556_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v_x_1556_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v_x_1556_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 0);
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1577_, lean_object* v_opt_1578_){
_start:
{
lean_object* v_name_1579_; lean_object* v_defValue_1580_; lean_object* v_map_1581_; lean_object* v___x_1582_; 
v_name_1579_ = lean_ctor_get(v_opt_1578_, 0);
v_defValue_1580_ = lean_ctor_get(v_opt_1578_, 1);
v_map_1581_ = lean_ctor_get(v_opts_1577_, 0);
v___x_1582_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1581_, v_name_1579_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_inc(v_defValue_1580_);
return v_defValue_1580_;
}
else
{
lean_object* v_val_1583_; 
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
if (lean_obj_tag(v_val_1583_) == 3)
{
lean_object* v_v_1584_; 
v_v_1584_ = lean_ctor_get(v_val_1583_, 0);
lean_inc(v_v_1584_);
lean_dec_ref_known(v_val_1583_, 1);
return v_v_1584_;
}
else
{
lean_dec(v_val_1583_);
lean_inc(v_defValue_1580_);
return v_defValue_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1585_, lean_object* v_opt_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1585_, v_opt_1586_);
lean_dec_ref(v_opt_1586_);
lean_dec_ref(v_opts_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_bs_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1591_ == 0)
{
return v_bs_1590_;
}
else
{
lean_object* v_v_1592_; lean_object* v_msg_1593_; lean_object* v___x_1594_; lean_object* v_bs_x27_1595_; size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v_v_1592_ = lean_array_uget_borrowed(v_bs_1590_, v_i_1589_);
v_msg_1593_ = lean_ctor_get(v_v_1592_, 1);
lean_inc_ref(v_msg_1593_);
v___x_1594_ = lean_unsigned_to_nat(0u);
v_bs_x27_1595_ = lean_array_uset(v_bs_1590_, v_i_1589_, v___x_1594_);
v___x_1596_ = ((size_t)1ULL);
v___x_1597_ = lean_usize_add(v_i_1589_, v___x_1596_);
v___x_1598_ = lean_array_uset(v_bs_x27_1595_, v_i_1589_, v_msg_1593_);
v_i_1589_ = v___x_1597_;
v_bs_1590_ = v___x_1598_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_){
_start:
{
size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1603_, v_i_boxed_1604_, v_bs_1602_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1606_, lean_object* v_data_1607_, lean_object* v_ref_1608_, lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_toCold_1615_; lean_object* v_currRecDepth_1616_; lean_object* v_ref_1617_; uint16_t v_optionFlags_1618_; uint8_t v_suppressElabErrors_1619_; uint8_t v_isRecordingDeps_1620_; lean_object* v_ref_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v_traceState_1624_; lean_object* v_traces_1625_; lean_object* v___x_1626_; size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; lean_object* v_msg_1630_; lean_object* v___x_1631_; lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1670_; 
v_toCold_1615_ = lean_ctor_get(v___y_1612_, 0);
v_currRecDepth_1616_ = lean_ctor_get(v___y_1612_, 1);
v_ref_1617_ = lean_ctor_get(v___y_1612_, 2);
v_optionFlags_1618_ = lean_ctor_get_uint16(v___y_1612_, sizeof(void*)*3);
v_suppressElabErrors_1619_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1620_ = lean_ctor_get_uint8(v___y_1612_, sizeof(void*)*3 + 3);
v_ref_1621_ = l_Lean_replaceRef(v_ref_1608_, v_ref_1617_);
lean_inc(v_currRecDepth_1616_);
lean_inc_ref(v_toCold_1615_);
v___x_1622_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1622_, 0, v_toCold_1615_);
lean_ctor_set(v___x_1622_, 1, v_currRecDepth_1616_);
lean_ctor_set(v___x_1622_, 2, v_ref_1621_);
lean_ctor_set_uint16(v___x_1622_, sizeof(void*)*3, v_optionFlags_1618_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*3 + 2, v_suppressElabErrors_1619_);
lean_ctor_set_uint8(v___x_1622_, sizeof(void*)*3 + 3, v_isRecordingDeps_1620_);
v___x_1623_ = lean_st_ref_get(v___y_1613_);
v_traceState_1624_ = lean_ctor_get(v___x_1623_, 4);
lean_inc_ref(v_traceState_1624_);
lean_dec(v___x_1623_);
v_traces_1625_ = lean_ctor_get(v_traceState_1624_, 0);
lean_inc_ref(v_traces_1625_);
lean_dec_ref(v_traceState_1624_);
v___x_1626_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1625_);
lean_dec_ref(v_traces_1625_);
v_sz_1627_ = lean_array_size(v___x_1626_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1627_, v___x_1628_, v___x_1626_);
v_msg_1630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1630_, 0, v_data_1607_);
lean_ctor_set(v_msg_1630_, 1, v_msg_1609_);
lean_ctor_set(v_msg_1630_, 2, v___x_1629_);
v___x_1631_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1630_, v___y_1610_, v___y_1611_, v___x_1622_, v___y_1613_);
lean_dec_ref_known(v___x_1622_, 3);
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1670_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1670_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v_traceState_1637_; lean_object* v_env_1638_; lean_object* v_nextMacroScope_1639_; lean_object* v_ngen_1640_; lean_object* v_auxDeclNGen_1641_; lean_object* v_cache_1642_; lean_object* v_recordedDeps_1643_; lean_object* v_messages_1644_; lean_object* v_infoState_1645_; lean_object* v_snapshotTasks_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1669_; 
v___x_1636_ = lean_st_ref_take(v___y_1613_);
v_traceState_1637_ = lean_ctor_get(v___x_1636_, 4);
v_env_1638_ = lean_ctor_get(v___x_1636_, 0);
v_nextMacroScope_1639_ = lean_ctor_get(v___x_1636_, 1);
v_ngen_1640_ = lean_ctor_get(v___x_1636_, 2);
v_auxDeclNGen_1641_ = lean_ctor_get(v___x_1636_, 3);
v_cache_1642_ = lean_ctor_get(v___x_1636_, 5);
v_recordedDeps_1643_ = lean_ctor_get(v___x_1636_, 6);
v_messages_1644_ = lean_ctor_get(v___x_1636_, 7);
v_infoState_1645_ = lean_ctor_get(v___x_1636_, 8);
v_snapshotTasks_1646_ = lean_ctor_get(v___x_1636_, 9);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1648_ = v___x_1636_;
v_isShared_1649_ = v_isSharedCheck_1669_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snapshotTasks_1646_);
lean_inc(v_infoState_1645_);
lean_inc(v_messages_1644_);
lean_inc(v_recordedDeps_1643_);
lean_inc(v_cache_1642_);
lean_inc(v_traceState_1637_);
lean_inc(v_auxDeclNGen_1641_);
lean_inc(v_ngen_1640_);
lean_inc(v_nextMacroScope_1639_);
lean_inc(v_env_1638_);
lean_dec(v___x_1636_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1669_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint64_t v_tid_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1667_; 
v_tid_1650_ = lean_ctor_get_uint64(v_traceState_1637_, sizeof(void*)*1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_traceState_1637_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v_traceState_1637_, 0);
lean_dec(v_unused_1668_);
v___x_1652_ = v_traceState_1637_;
v_isShared_1653_ = v_isSharedCheck_1667_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v_traceState_1637_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1667_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_ref_1608_);
lean_ctor_set(v___x_1655_, 1, v_a_1632_);
v___x_1656_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1606_, v___x_1655_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v___x_1656_);
v___x_1658_ = v___x_1652_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1656_);
lean_ctor_set_uint64(v_reuseFailAlloc_1666_, sizeof(void*)*1, v_tid_1650_);
v___x_1658_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 4, v___x_1658_);
v___x_1660_ = v___x_1648_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_env_1638_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_nextMacroScope_1639_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_ngen_1640_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_auxDeclNGen_1641_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 5, v_cache_1642_);
lean_ctor_set(v_reuseFailAlloc_1665_, 6, v_recordedDeps_1643_);
lean_ctor_set(v_reuseFailAlloc_1665_, 7, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1665_, 8, v_infoState_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 9, v_snapshotTasks_1646_);
v___x_1660_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_st_ref_put(v___y_1613_, v___x_1660_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1654_);
v___x_1663_ = v___x_1634_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v___x_1654_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1671_, lean_object* v_data_1672_, lean_object* v_ref_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1671_, v_data_1672_, v_ref_1673_, v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
return v_res_1680_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1681_; double v___x_1682_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_float_of_nat(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1686_; double v___x_1687_; 
v___x_1686_ = lean_unsigned_to_nat(1000u);
v___x_1687_ = lean_float_of_nat(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1688_, uint8_t v_collapsed_1689_, lean_object* v_tag_1690_, lean_object* v_opts_1691_, uint8_t v_clsEnabled_1692_, lean_object* v_oldTraces_1693_, lean_object* v_msg_1694_, lean_object* v_resStartStop_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_fst_1701_; lean_object* v_snd_1702_; lean_object* v___y_1704_; lean_object* v___y_1705_; lean_object* v_data_1706_; lean_object* v_fst_1709_; lean_object* v_snd_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; lean_object* v___y_1714_; lean_object* v_a_1715_; uint8_t v___y_1730_; double v___y_1762_; 
v_fst_1701_ = lean_ctor_get(v_resStartStop_1695_, 0);
lean_inc(v_fst_1701_);
v_snd_1702_ = lean_ctor_get(v_resStartStop_1695_, 1);
lean_inc(v_snd_1702_);
lean_dec_ref(v_resStartStop_1695_);
v_fst_1709_ = lean_ctor_get(v_snd_1702_, 0);
lean_inc(v_fst_1709_);
v_snd_1710_ = lean_ctor_get(v_snd_1702_, 1);
lean_inc(v_snd_1710_);
lean_dec(v_snd_1702_);
v___x_1711_ = l_Lean_trace_profiler;
v___x_1712_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1691_, v___x_1711_);
if (v___x_1712_ == 0)
{
v___y_1730_ = v___x_1712_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1768_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1691_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; double v___x_1771_; double v___x_1772_; double v___x_1773_; 
v___x_1769_ = l_Lean_trace_profiler_threshold;
v___x_1770_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1691_, v___x_1769_);
v___x_1771_ = lean_float_of_nat(v___x_1770_);
v___x_1772_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1773_ = lean_float_div(v___x_1771_, v___x_1772_);
v___y_1762_ = v___x_1773_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; double v___x_1776_; 
v___x_1774_ = l_Lean_trace_profiler_threshold;
v___x_1775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1691_, v___x_1774_);
v___x_1776_ = lean_float_of_nat(v___x_1775_);
v___y_1762_ = v___x_1776_;
goto v___jp_1761_;
}
}
v___jp_1703_:
{
lean_object* v___x_1707_; 
lean_inc(v___y_1705_);
v___x_1707_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1693_, v_data_1706_, v___y_1705_, v___y_1704_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; 
lean_dec_ref_known(v___x_1707_, 1);
v___x_1708_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1701_);
return v___x_1708_;
}
else
{
lean_dec(v_fst_1701_);
return v___x_1707_;
}
}
v___jp_1713_:
{
uint8_t v_result_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; double v___x_1719_; lean_object* v_data_1720_; 
v_result_1716_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1701_);
v___x_1717_ = lean_box(v_result_1716_);
v___x_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
v___x_1719_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1690_);
lean_inc_ref(v___x_1718_);
lean_inc(v_cls_1688_);
v_data_1720_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1720_, 0, v_cls_1688_);
lean_ctor_set(v_data_1720_, 1, v___x_1718_);
lean_ctor_set(v_data_1720_, 2, v_tag_1690_);
lean_ctor_set_float(v_data_1720_, sizeof(void*)*3, v___x_1719_);
lean_ctor_set_float(v_data_1720_, sizeof(void*)*3 + 8, v___x_1719_);
lean_ctor_set_uint8(v_data_1720_, sizeof(void*)*3 + 16, v_collapsed_1689_);
if (v___x_1712_ == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec_ref(v_tag_1690_);
lean_dec(v_cls_1688_);
v___y_1704_ = v_a_1715_;
v___y_1705_ = v___y_1714_;
v_data_1706_ = v_data_1720_;
goto v___jp_1703_;
}
else
{
lean_object* v_data_1721_; double v___x_1722_; double v___x_1723_; 
lean_dec_ref_known(v_data_1720_, 3);
v_data_1721_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1721_, 0, v_cls_1688_);
lean_ctor_set(v_data_1721_, 1, v___x_1718_);
lean_ctor_set(v_data_1721_, 2, v_tag_1690_);
v___x_1722_ = lean_unbox_float(v_fst_1709_);
lean_dec(v_fst_1709_);
lean_ctor_set_float(v_data_1721_, sizeof(void*)*3, v___x_1722_);
v___x_1723_ = lean_unbox_float(v_snd_1710_);
lean_dec(v_snd_1710_);
lean_ctor_set_float(v_data_1721_, sizeof(void*)*3 + 8, v___x_1723_);
lean_ctor_set_uint8(v_data_1721_, sizeof(void*)*3 + 16, v_collapsed_1689_);
v___y_1704_ = v_a_1715_;
v___y_1705_ = v___y_1714_;
v_data_1706_ = v_data_1721_;
goto v___jp_1703_;
}
}
v___jp_1724_:
{
lean_object* v_ref_1725_; lean_object* v___x_1726_; 
v_ref_1725_ = lean_ctor_get(v___y_1698_, 2);
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v_fst_1701_);
v___x_1726_ = lean_apply_6(v_msg_1694_, v_fst_1701_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, lean_box(0));
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___y_1714_ = v_ref_1725_;
v_a_1715_ = v_a_1727_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1728_; 
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1714_ = v_ref_1725_;
v_a_1715_ = v___x_1728_;
goto v___jp_1713_;
}
}
v___jp_1729_:
{
if (v_clsEnabled_1692_ == 0)
{
if (v___y_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v_traceState_1732_; lean_object* v_env_1733_; lean_object* v_nextMacroScope_1734_; lean_object* v_ngen_1735_; lean_object* v_auxDeclNGen_1736_; lean_object* v_cache_1737_; lean_object* v_recordedDeps_1738_; lean_object* v_messages_1739_; lean_object* v_infoState_1740_; lean_object* v_snapshotTasks_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_snd_1710_);
lean_dec(v_fst_1709_);
lean_dec_ref(v_msg_1694_);
lean_dec_ref(v_tag_1690_);
lean_dec(v_cls_1688_);
v___x_1731_ = lean_st_ref_take(v___y_1699_);
v_traceState_1732_ = lean_ctor_get(v___x_1731_, 4);
v_env_1733_ = lean_ctor_get(v___x_1731_, 0);
v_nextMacroScope_1734_ = lean_ctor_get(v___x_1731_, 1);
v_ngen_1735_ = lean_ctor_get(v___x_1731_, 2);
v_auxDeclNGen_1736_ = lean_ctor_get(v___x_1731_, 3);
v_cache_1737_ = lean_ctor_get(v___x_1731_, 5);
v_recordedDeps_1738_ = lean_ctor_get(v___x_1731_, 6);
v_messages_1739_ = lean_ctor_get(v___x_1731_, 7);
v_infoState_1740_ = lean_ctor_get(v___x_1731_, 8);
v_snapshotTasks_1741_ = lean_ctor_get(v___x_1731_, 9);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1743_ = v___x_1731_;
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_snapshotTasks_1741_);
lean_inc(v_infoState_1740_);
lean_inc(v_messages_1739_);
lean_inc(v_recordedDeps_1738_);
lean_inc(v_cache_1737_);
lean_inc(v_traceState_1732_);
lean_inc(v_auxDeclNGen_1736_);
lean_inc(v_ngen_1735_);
lean_inc(v_nextMacroScope_1734_);
lean_inc(v_env_1733_);
lean_dec(v___x_1731_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1760_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
uint64_t v_tid_1745_; lean_object* v_traces_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v_tid_1745_ = lean_ctor_get_uint64(v_traceState_1732_, sizeof(void*)*1);
v_traces_1746_ = lean_ctor_get(v_traceState_1732_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_traceState_1732_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1748_ = v_traceState_1732_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_traces_1746_);
lean_dec(v_traceState_1732_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1693_, v_traces_1746_);
lean_dec_ref(v_traces_1746_);
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 0, v___x_1750_);
v___x_1752_ = v___x_1748_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1750_);
lean_ctor_set_uint64(v_reuseFailAlloc_1758_, sizeof(void*)*1, v_tid_1745_);
v___x_1752_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 4, v___x_1752_);
v___x_1754_ = v___x_1743_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_env_1733_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_nextMacroScope_1734_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_ngen_1735_);
lean_ctor_set(v_reuseFailAlloc_1757_, 3, v_auxDeclNGen_1736_);
lean_ctor_set(v_reuseFailAlloc_1757_, 4, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1757_, 5, v_cache_1737_);
lean_ctor_set(v_reuseFailAlloc_1757_, 6, v_recordedDeps_1738_);
lean_ctor_set(v_reuseFailAlloc_1757_, 7, v_messages_1739_);
lean_ctor_set(v_reuseFailAlloc_1757_, 8, v_infoState_1740_);
lean_ctor_set(v_reuseFailAlloc_1757_, 9, v_snapshotTasks_1741_);
v___x_1754_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_st_ref_put(v___y_1699_, v___x_1754_);
v___x_1756_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1701_);
return v___x_1756_;
}
}
}
}
}
else
{
goto v___jp_1724_;
}
}
else
{
goto v___jp_1724_;
}
}
v___jp_1761_:
{
double v___x_1763_; double v___x_1764_; double v___x_1765_; uint8_t v___x_1766_; 
v___x_1763_ = lean_unbox_float(v_snd_1710_);
v___x_1764_ = lean_unbox_float(v_fst_1709_);
v___x_1765_ = lean_float_sub(v___x_1763_, v___x_1764_);
v___x_1766_ = lean_float_decLt(v___y_1762_, v___x_1765_);
v___y_1730_ = v___x_1766_;
goto v___jp_1729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1777_, lean_object* v_collapsed_1778_, lean_object* v_tag_1779_, lean_object* v_opts_1780_, lean_object* v_clsEnabled_1781_, lean_object* v_oldTraces_1782_, lean_object* v_msg_1783_, lean_object* v_resStartStop_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
uint8_t v_collapsed_boxed_1790_; uint8_t v_clsEnabled_boxed_1791_; lean_object* v_res_1792_; 
v_collapsed_boxed_1790_ = lean_unbox(v_collapsed_1778_);
v_clsEnabled_boxed_1791_ = lean_unbox(v_clsEnabled_1781_);
v_res_1792_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1777_, v_collapsed_boxed_1790_, v_tag_1779_, v_opts_1780_, v_clsEnabled_boxed_1791_, v_oldTraces_1782_, v_msg_1783_, v_resStartStop_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_opts_1780_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v___x_1796_, lean_object* v_a_1797_, lean_object* v_b_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_lt(v_a_1797_, v_upperBound_1793_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec(v_a_1797_);
lean_dec(v___x_1796_);
lean_dec(v___x_1795_);
lean_dec(v___x_1794_);
v___x_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1805_, 0, v_b_1798_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_unsigned_to_nat(1u);
v___x_1808_ = lean_nat_add(v_a_1797_, v___x_1807_);
lean_dec(v_a_1797_);
lean_inc_n(v___x_1808_, 2);
lean_inc(v___x_1794_);
v___x_1809_ = lean_name_append_index_after(v___x_1794_, v___x_1808_);
lean_inc(v___x_1795_);
v___x_1810_ = lean_name_append_index_after(v___x_1795_, v___x_1808_);
lean_inc(v___x_1796_);
v___x_1811_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1809_, v___x_1796_, v___x_1810_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref_known(v___x_1811_, 1);
v_a_1797_ = v___x_1808_;
v_b_1798_ = v___x_1806_;
goto _start;
}
else
{
lean_dec(v___x_1808_);
lean_dec(v___x_1796_);
lean_dec(v___x_1795_);
lean_dec(v___x_1794_);
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1813_, v___x_1814_, v___x_1815_, v___x_1816_, v_a_1817_, v_b_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v_upperBound_1813_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1835_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1836_ = l_Lean_Name_append(v___x_1835_, v___x_1834_);
return v___x_1836_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1837_; double v___x_1838_; 
v___x_1837_ = lean_unsigned_to_nat(1000000000u);
v___x_1838_ = lean_float_of_nat(v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_toCold_1845_; lean_object* v_options_1846_; lean_object* v_inheritedTraceOptions_1847_; uint8_t v_hasTrace_1848_; lean_object* v___x_1849_; 
v_toCold_1845_ = lean_ctor_get(v_a_1842_, 0);
v_options_1846_ = lean_ctor_get(v_toCold_1845_, 2);
v_inheritedTraceOptions_1847_ = lean_ctor_get(v_toCold_1845_, 11);
v_hasTrace_1848_ = lean_ctor_get_uint8(v_options_1846_, sizeof(void*)*1);
v___x_1849_ = lean_box(0);
if (v_hasTrace_1848_ == 0)
{
lean_object* v___x_1850_; 
lean_inc(v_indName_1839_);
v___x_1850_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1914_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
if (lean_obj_tag(v_a_1851_) == 5)
{
lean_object* v_val_1855_; uint8_t v_isRec_1856_; 
v_val_1855_ = lean_ctor_get(v_a_1851_, 0);
lean_inc_ref(v_val_1855_);
lean_dec_ref_known(v_a_1851_, 1);
v_isRec_1856_ = lean_ctor_get_uint8(v_val_1855_, sizeof(void*)*6);
if (v_isRec_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec_ref(v_val_1855_);
lean_dec(v_indName_1839_);
v___x_1857_ = lean_box(0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1857_);
v___x_1859_ = v___x_1853_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
else
{
lean_object* v_toConstantVal_1861_; lean_object* v_numParams_1862_; lean_object* v_all_1863_; lean_object* v_numNested_1864_; lean_object* v_type_1865_; lean_object* v___x_1866_; 
lean_del_object(v___x_1853_);
v_toConstantVal_1861_ = lean_ctor_get(v_val_1855_, 0);
lean_inc_ref(v_toConstantVal_1861_);
v_numParams_1862_ = lean_ctor_get(v_val_1855_, 1);
lean_inc(v_numParams_1862_);
v_all_1863_ = lean_ctor_get(v_val_1855_, 3);
lean_inc(v_all_1863_);
v_numNested_1864_ = lean_ctor_get(v_val_1855_, 5);
lean_inc(v_numNested_1864_);
lean_dec_ref(v_val_1855_);
v_type_1865_ = lean_ctor_get(v_toConstantVal_1861_, 2);
lean_inc_ref(v_type_1865_);
lean_dec_ref(v_toConstantVal_1861_);
v___x_1866_ = l_Lean_Meta_isPropFormerType(v_type_1865_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1901_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1901_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1901_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_unbox(v_a_1867_);
lean_dec(v_a_1867_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_del_object(v___x_1869_);
lean_inc_n(v_indName_1839_, 2);
v___x_1872_ = l_Lean_mkRecName(v_indName_1839_);
v___x_1873_ = l_Lean_mkBelowName(v_indName_1839_);
lean_inc(v___x_1873_);
lean_inc(v_numParams_1862_);
lean_inc(v___x_1872_);
v___x_1874_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1872_, v_numParams_1862_, v___x_1873_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1895_; 
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1874_, 0);
lean_dec(v_unused_1896_);
v___x_1876_ = v___x_1874_;
v_isShared_1877_ = v_isSharedCheck_1895_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v___x_1874_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1895_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = l_List_get_x21Internal___redArg(v___x_1849_, v_all_1863_, v___x_1878_);
lean_dec(v_all_1863_);
v___x_1880_ = lean_name_eq(v___x_1879_, v_indName_1839_);
lean_dec(v_indName_1839_);
lean_dec(v___x_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec(v___x_1873_);
lean_dec(v___x_1872_);
lean_dec(v_numNested_1864_);
lean_dec(v_numParams_1862_);
v___x_1881_ = lean_box(0);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1881_);
v___x_1883_ = v___x_1876_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_del_object(v___x_1876_);
v___x_1885_ = lean_box(0);
v___x_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1864_, v___x_1872_, v___x_1873_, v_numParams_1862_, v___x_1878_, v___x_1885_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_numNested_1864_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; 
v_unused_1894_ = lean_ctor_get(v___x_1886_, 0);
lean_dec(v_unused_1894_);
v___x_1888_ = v___x_1886_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v___x_1886_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1885_);
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1885_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
return v___x_1886_;
}
}
}
}
else
{
lean_dec(v___x_1873_);
lean_dec(v___x_1872_);
lean_dec(v_numNested_1864_);
lean_dec(v_all_1863_);
lean_dec(v_numParams_1862_);
lean_dec(v_indName_1839_);
return v___x_1874_;
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_numNested_1864_);
lean_dec(v_all_1863_);
lean_dec(v_numParams_1862_);
lean_dec(v_indName_1839_);
v___x_1897_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1897_);
v___x_1899_ = v___x_1869_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_numNested_1864_);
lean_dec(v_all_1863_);
lean_dec(v_numParams_1862_);
lean_dec(v_indName_1839_);
v_a_1902_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1866_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1866_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
lean_dec(v_a_1851_);
lean_dec(v_indName_1839_);
v___x_1910_ = lean_box(0);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1910_);
v___x_1912_ = v___x_1853_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_indName_1839_);
v_a_1915_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1850_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1850_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
else
{
lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v_a_1931_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v_a_1946_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_a_1951_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v_a_1956_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_a_1968_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v_a_1973_; 
lean_inc(v_indName_1839_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1923_, 0, v_indName_1839_);
v___x_1924_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1925_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1926_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1847_, v_options_1846_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = l_Lean_trace_profiler;
v___x_2041_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1846_, v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; 
lean_dec_ref(v___f_1923_);
lean_inc(v_indName_1839_);
v___x_2042_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2106_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2106_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2106_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
if (lean_obj_tag(v_a_2043_) == 5)
{
lean_object* v_val_2047_; uint8_t v_isRec_2048_; 
v_val_2047_ = lean_ctor_get(v_a_2043_, 0);
lean_inc_ref(v_val_2047_);
lean_dec_ref_known(v_a_2043_, 1);
v_isRec_2048_ = lean_ctor_get_uint8(v_val_2047_, sizeof(void*)*6);
if (v_isRec_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
lean_dec_ref(v_val_2047_);
lean_dec(v_indName_1839_);
v___x_2049_ = lean_box(0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2049_);
v___x_2051_ = v___x_2045_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
else
{
lean_object* v_toConstantVal_2053_; lean_object* v_numParams_2054_; lean_object* v_all_2055_; lean_object* v_numNested_2056_; lean_object* v_type_2057_; lean_object* v___x_2058_; 
lean_del_object(v___x_2045_);
v_toConstantVal_2053_ = lean_ctor_get(v_val_2047_, 0);
lean_inc_ref(v_toConstantVal_2053_);
v_numParams_2054_ = lean_ctor_get(v_val_2047_, 1);
lean_inc(v_numParams_2054_);
v_all_2055_ = lean_ctor_get(v_val_2047_, 3);
lean_inc(v_all_2055_);
v_numNested_2056_ = lean_ctor_get(v_val_2047_, 5);
lean_inc(v_numNested_2056_);
lean_dec_ref(v_val_2047_);
v_type_2057_ = lean_ctor_get(v_toConstantVal_2053_, 2);
lean_inc_ref(v_type_2057_);
lean_dec_ref(v_toConstantVal_2053_);
v___x_2058_ = l_Lean_Meta_isPropFormerType(v_type_2057_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2093_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2093_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2093_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_unbox(v_a_2059_);
lean_dec(v_a_2059_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_del_object(v___x_2061_);
lean_inc_n(v_indName_1839_, 2);
v___x_2064_ = l_Lean_mkRecName(v_indName_1839_);
v___x_2065_ = l_Lean_mkBelowName(v_indName_1839_);
lean_inc(v___x_2065_);
lean_inc(v_numParams_2054_);
lean_inc(v___x_2064_);
v___x_2066_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2064_, v_numParams_2054_, v___x_2065_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2088_);
v___x_2068_ = v___x_2066_;
v_isShared_2069_ = v_isSharedCheck_2087_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v___x_2066_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2087_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = l_List_get_x21Internal___redArg(v___x_1849_, v_all_2055_, v___x_2070_);
lean_dec(v_all_2055_);
v___x_2072_ = lean_name_eq(v___x_2071_, v_indName_1839_);
lean_dec(v_indName_1839_);
lean_dec(v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_dec(v___x_2065_);
lean_dec(v___x_2064_);
lean_dec(v_numNested_2056_);
lean_dec(v_numParams_2054_);
v___x_2073_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2073_);
v___x_2075_ = v___x_2068_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_del_object(v___x_2068_);
v___x_2077_ = lean_box(0);
v___x_2078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2056_, v___x_2064_, v___x_2065_, v_numParams_2054_, v___x_2070_, v___x_2077_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_numNested_2056_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2078_, 0);
lean_dec(v_unused_2086_);
v___x_2080_ = v___x_2078_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v___x_2078_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2077_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2077_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
return v___x_2078_;
}
}
}
}
else
{
lean_dec(v___x_2065_);
lean_dec(v___x_2064_);
lean_dec(v_numNested_2056_);
lean_dec(v_all_2055_);
lean_dec(v_numParams_2054_);
lean_dec(v_indName_1839_);
return v___x_2066_;
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec(v_numNested_2056_);
lean_dec(v_all_2055_);
lean_dec(v_numParams_2054_);
lean_dec(v_indName_1839_);
v___x_2089_ = lean_box(0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2089_);
v___x_2091_ = v___x_2061_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec(v_numNested_2056_);
lean_dec(v_all_2055_);
lean_dec(v_numParams_2054_);
lean_dec(v_indName_1839_);
v_a_2094_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2058_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2058_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_dec(v_a_2043_);
lean_dec(v_indName_1839_);
v___x_2102_ = lean_box(0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2102_);
v___x_2104_ = v___x_2045_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2102_);
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
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec(v_indName_1839_);
v_a_2107_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2042_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2042_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
goto v___jp_1975_;
}
}
else
{
goto v___jp_1975_;
}
v___jp_1928_:
{
lean_object* v___x_1932_; double v___x_1933_; double v___x_1934_; double v___x_1935_; double v___x_1936_; double v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1932_ = lean_io_mono_nanos_now();
v___x_1933_ = lean_float_of_nat(v___y_1930_);
v___x_1934_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1935_ = lean_float_div(v___x_1933_, v___x_1934_);
v___x_1936_ = lean_float_of_nat(v___x_1932_);
v___x_1937_ = lean_float_div(v___x_1936_, v___x_1934_);
v___x_1938_ = lean_box_float(v___x_1935_);
v___x_1939_ = lean_box_float(v___x_1937_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1931_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1924_, v_hasTrace_1848_, v___x_1925_, v_options_1846_, v___x_1927_, v___y_1929_, v___f_1923_, v___x_1941_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1942_;
}
v___jp_1943_:
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1946_);
v___y_1929_ = v___y_1944_;
v___y_1930_ = v___y_1945_;
v_a_1931_ = v___x_1947_;
goto v___jp_1928_;
}
v___jp_1948_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1951_);
v___y_1929_ = v___y_1949_;
v___y_1930_ = v___y_1950_;
v_a_1931_ = v___x_1952_;
goto v___jp_1928_;
}
v___jp_1953_:
{
lean_object* v___x_1957_; double v___x_1958_; double v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1957_ = lean_io_get_num_heartbeats();
v___x_1958_ = lean_float_of_nat(v___y_1955_);
v___x_1959_ = lean_float_of_nat(v___x_1957_);
v___x_1960_ = lean_box_float(v___x_1958_);
v___x_1961_ = lean_box_float(v___x_1959_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1963_, 0, v_a_1956_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1924_, v_hasTrace_1848_, v___x_1925_, v_options_1846_, v___x_1927_, v___y_1954_, v___f_1923_, v___x_1963_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1964_;
}
v___jp_1965_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1968_);
v___y_1954_ = v___y_1966_;
v___y_1955_ = v___y_1967_;
v_a_1956_ = v___x_1969_;
goto v___jp_1953_;
}
v___jp_1970_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1973_);
v___y_1954_ = v___y_1971_;
v___y_1955_ = v___y_1972_;
v_a_1956_ = v___x_1974_;
goto v___jp_1953_;
}
v___jp_1975_:
{
lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1976_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1843_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___x_1978_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1979_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1846_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1839_);
v___x_1981_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
if (lean_obj_tag(v_a_1982_) == 5)
{
lean_object* v_val_1983_; uint8_t v_isRec_1984_; 
v_val_1983_ = lean_ctor_get(v_a_1982_, 0);
lean_inc_ref(v_val_1983_);
lean_dec_ref_known(v_a_1982_, 1);
v_isRec_1984_ = lean_ctor_get_uint8(v_val_1983_, sizeof(void*)*6);
if (v_isRec_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec_ref(v_val_1983_);
lean_dec(v_indName_1839_);
v___x_1985_ = lean_box(0);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v___x_1985_;
goto v___jp_1943_;
}
else
{
lean_object* v_toConstantVal_1986_; lean_object* v_numParams_1987_; lean_object* v_all_1988_; lean_object* v_numNested_1989_; lean_object* v_type_1990_; lean_object* v___x_1991_; 
v_toConstantVal_1986_ = lean_ctor_get(v_val_1983_, 0);
lean_inc_ref(v_toConstantVal_1986_);
v_numParams_1987_ = lean_ctor_get(v_val_1983_, 1);
lean_inc(v_numParams_1987_);
v_all_1988_ = lean_ctor_get(v_val_1983_, 3);
lean_inc(v_all_1988_);
v_numNested_1989_ = lean_ctor_get(v_val_1983_, 5);
lean_inc(v_numNested_1989_);
lean_dec_ref(v_val_1983_);
v_type_1990_ = lean_ctor_get(v_toConstantVal_1986_, 2);
lean_inc_ref(v_type_1990_);
lean_dec_ref(v_toConstantVal_1986_);
v___x_1991_ = l_Lean_Meta_isPropFormerType(v_type_1990_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; uint8_t v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___x_1993_ = lean_unbox(v_a_1992_);
lean_dec(v_a_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_n(v_indName_1839_, 2);
v___x_1994_ = l_Lean_mkRecName(v_indName_1839_);
v___x_1995_ = l_Lean_mkBelowName(v_indName_1839_);
lean_inc(v___x_1995_);
lean_inc(v_numParams_1987_);
lean_inc(v___x_1994_);
v___x_1996_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1994_, v_numParams_1987_, v___x_1995_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
lean_dec_ref_known(v___x_1996_, 1);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = l_List_get_x21Internal___redArg(v___x_1849_, v_all_1988_, v___x_1997_);
lean_dec(v_all_1988_);
v___x_1999_ = lean_name_eq(v___x_1998_, v_indName_1839_);
lean_dec(v_indName_1839_);
lean_dec(v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec(v___x_1995_);
lean_dec(v___x_1994_);
lean_dec(v_numNested_1989_);
lean_dec(v_numParams_1987_);
v___x_2000_ = lean_box(0);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v___x_2000_;
goto v___jp_1943_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = lean_box(0);
v___x_2002_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1989_, v___x_1994_, v___x_1995_, v_numParams_1987_, v___x_1997_, v___x_2001_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_numNested_1989_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_dec_ref_known(v___x_2002_, 1);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v___x_2001_;
goto v___jp_1943_;
}
else
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1949_ = v_a_1977_;
v___y_1950_ = v___x_1980_;
v_a_1951_ = v_a_2003_;
goto v___jp_1948_;
}
}
}
else
{
lean_dec(v___x_1995_);
lean_dec(v___x_1994_);
lean_dec(v_numNested_1989_);
lean_dec(v_all_1988_);
lean_dec(v_numParams_1987_);
lean_dec(v_indName_1839_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_2004_; 
v_a_2004_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v_a_2004_;
goto v___jp_1943_;
}
else
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1949_ = v_a_1977_;
v___y_1950_ = v___x_1980_;
v_a_1951_ = v_a_2005_;
goto v___jp_1948_;
}
}
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_numNested_1989_);
lean_dec(v_all_1988_);
lean_dec(v_numParams_1987_);
lean_dec(v_indName_1839_);
v___x_2006_ = lean_box(0);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v___x_2006_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2007_; 
lean_dec(v_numNested_1989_);
lean_dec(v_all_1988_);
lean_dec(v_numParams_1987_);
lean_dec(v_indName_1839_);
v_a_2007_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1949_ = v_a_1977_;
v___y_1950_ = v___x_1980_;
v_a_1951_ = v_a_2007_;
goto v___jp_1948_;
}
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_a_1982_);
lean_dec(v_indName_1839_);
v___x_2008_ = lean_box(0);
v___y_1944_ = v_a_1977_;
v___y_1945_ = v___x_1980_;
v_a_1946_ = v___x_2008_;
goto v___jp_1943_;
}
}
else
{
lean_object* v_a_2009_; 
lean_dec(v_indName_1839_);
v_a_2009_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_1981_, 1);
v___y_1949_ = v_a_1977_;
v___y_1950_ = v___x_1980_;
v_a_1951_ = v_a_2009_;
goto v___jp_1948_;
}
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1839_);
v___x_2011_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
if (lean_obj_tag(v_a_2012_) == 5)
{
lean_object* v_val_2013_; uint8_t v_isRec_2014_; 
v_val_2013_ = lean_ctor_get(v_a_2012_, 0);
lean_inc_ref(v_val_2013_);
lean_dec_ref_known(v_a_2012_, 1);
v_isRec_2014_ = lean_ctor_get_uint8(v_val_2013_, sizeof(void*)*6);
if (v_isRec_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec_ref(v_val_2013_);
lean_dec(v_indName_1839_);
v___x_2015_ = lean_box(0);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v___x_2015_;
goto v___jp_1965_;
}
else
{
lean_object* v_toConstantVal_2016_; lean_object* v_numParams_2017_; lean_object* v_all_2018_; lean_object* v_numNested_2019_; lean_object* v_type_2020_; lean_object* v___x_2021_; 
v_toConstantVal_2016_ = lean_ctor_get(v_val_2013_, 0);
lean_inc_ref(v_toConstantVal_2016_);
v_numParams_2017_ = lean_ctor_get(v_val_2013_, 1);
lean_inc(v_numParams_2017_);
v_all_2018_ = lean_ctor_get(v_val_2013_, 3);
lean_inc(v_all_2018_);
v_numNested_2019_ = lean_ctor_get(v_val_2013_, 5);
lean_inc(v_numNested_2019_);
lean_dec_ref(v_val_2013_);
v_type_2020_ = lean_ctor_get(v_toConstantVal_2016_, 2);
lean_inc_ref(v_type_2020_);
lean_dec_ref(v_toConstantVal_2016_);
v___x_2021_ = l_Lean_Meta_isPropFormerType(v_type_2020_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_inc_n(v_indName_1839_, 2);
v___x_2024_ = l_Lean_mkRecName(v_indName_1839_);
v___x_2025_ = l_Lean_mkBelowName(v_indName_1839_);
lean_inc(v___x_2025_);
lean_inc(v_numParams_2017_);
lean_inc(v___x_2024_);
v___x_2026_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2024_, v_numParams_2017_, v___x_2025_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
lean_dec_ref_known(v___x_2026_, 1);
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = l_List_get_x21Internal___redArg(v___x_1849_, v_all_2018_, v___x_2027_);
lean_dec(v_all_2018_);
v___x_2029_ = lean_name_eq(v___x_2028_, v_indName_1839_);
lean_dec(v_indName_1839_);
lean_dec(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec(v___x_2025_);
lean_dec(v___x_2024_);
lean_dec(v_numNested_2019_);
lean_dec(v_numParams_2017_);
v___x_2030_ = lean_box(0);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v___x_2030_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_box(0);
v___x_2032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2019_, v___x_2024_, v___x_2025_, v_numParams_2017_, v___x_2027_, v___x_2031_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_numNested_2019_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_dec_ref_known(v___x_2032_, 1);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v___x_2031_;
goto v___jp_1965_;
}
else
{
lean_object* v_a_2033_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___y_1971_ = v_a_1977_;
v___y_1972_ = v___x_2010_;
v_a_1973_ = v_a_2033_;
goto v___jp_1970_;
}
}
}
else
{
lean_dec(v___x_2025_);
lean_dec(v___x_2024_);
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1839_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2026_, 1);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v_a_2034_;
goto v___jp_1965_;
}
else
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2026_, 1);
v___y_1971_ = v_a_1977_;
v___y_1972_ = v___x_2010_;
v_a_1973_ = v_a_2035_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v___x_2036_; 
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1839_);
v___x_2036_ = lean_box(0);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v___x_2036_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2037_; 
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1839_);
v_a_2037_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2021_, 1);
v___y_1971_ = v_a_1977_;
v___y_1972_ = v___x_2010_;
v_a_1973_ = v_a_2037_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v___x_2038_; 
lean_dec(v_a_2012_);
lean_dec(v_indName_1839_);
v___x_2038_ = lean_box(0);
v___y_1966_ = v_a_1977_;
v___y_1967_ = v___x_2010_;
v_a_1968_ = v___x_2038_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2039_; 
lean_dec(v_indName_1839_);
v_a_2039_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1971_ = v_a_1977_;
v___y_1972_ = v___x_2010_;
v_a_1973_ = v_a_2039_;
goto v___jp_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_mkBelow(v_indName_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2122_, lean_object* v___x_2123_, lean_object* v___x_2124_, lean_object* v___x_2125_, lean_object* v_inst_2126_, lean_object* v_R_2127_, lean_object* v_a_2128_, lean_object* v_b_2129_, lean_object* v_c_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2122_, v___x_2123_, v___x_2124_, v___x_2125_, v_a_2128_, v_b_2129_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2137_, lean_object* v___x_2138_, lean_object* v___x_2139_, lean_object* v___x_2140_, lean_object* v_inst_2141_, lean_object* v_R_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_, lean_object* v_c_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2137_, v___x_2138_, v___x_2139_, v___x_2140_, v_inst_2141_, v_R_2142_, v_a_2143_, v_b_2144_, v_c_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v_upperBound_2137_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2152_, lean_object* v_x_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2153_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_x_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2160_, v_x_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
if (lean_obj_tag(v_a_2168_) == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = l_List_reverse___redArg(v_a_2169_);
return v___x_2170_;
}
else
{
lean_object* v_head_2171_; lean_object* v_tail_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2181_; 
v_head_2171_ = lean_ctor_get(v_a_2168_, 0);
v_tail_2172_ = lean_ctor_get(v_a_2168_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2168_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2174_ = v_a_2168_;
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_tail_2172_);
lean_inc(v_head_2171_);
lean_dec(v_a_2168_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = l_Lean_MessageData_ofExpr(v_head_2171_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_a_2169_);
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2176_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_a_2169_);
v___x_2178_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
v_a_2168_ = v_tail_2172_;
v_a_2169_ = v___x_2178_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2182_, lean_object* v_v_2183_, lean_object* v_i_2184_){
_start:
{
lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2185_ = lean_array_get_size(v_xs_2182_);
v___x_2186_ = lean_nat_dec_lt(v_i_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_i_2184_);
v___x_2187_ = lean_box(0);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = lean_array_fget_borrowed(v_xs_2182_, v_i_2184_);
v___x_2189_ = lean_expr_eqv(v___x_2188_, v_v_2183_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_add(v_i_2184_, v___x_2190_);
lean_dec(v_i_2184_);
v_i_2184_ = v___x_2191_;
goto _start;
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_i_2184_);
return v___x_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2194_, lean_object* v_v_2195_, lean_object* v_i_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2194_, v_v_2195_, v_i_2196_);
lean_dec_ref(v_v_2195_);
lean_dec_ref(v_xs_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2198_, lean_object* v_v_2199_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2198_, v_v_2199_, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2202_, lean_object* v_v_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2202_, v_v_2203_);
lean_dec_ref(v_v_2203_);
lean_dec_ref(v_xs_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2205_, lean_object* v_v_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2205_, v_v_2206_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_box(0);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_val_2209_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2207_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_val_2209_);
lean_dec(v___x_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_val_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2217_, lean_object* v_v_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2217_, v_v_2218_);
lean_dec_ref(v_v_2218_);
lean_dec_ref(v_xs_2217_);
return v_res_2219_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2226_, lean_object* v_prods_2227_, lean_object* v_motives_2228_, lean_object* v_fs_2229_, lean_object* v_minor__type_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
if (lean_obj_tag(v_x_2231_) == 5)
{
lean_object* v_fn_2239_; lean_object* v_arg_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_fn_2239_ = lean_ctor_get(v_x_2231_, 0);
lean_inc_ref(v_fn_2239_);
v_arg_2240_ = lean_ctor_get(v_x_2231_, 1);
lean_inc_ref(v_arg_2240_);
lean_dec_ref_known(v_x_2231_, 2);
v___x_2241_ = lean_array_set(v_x_2232_, v_x_2233_, v_arg_2240_);
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_nat_sub(v_x_2233_, v___x_2242_);
lean_dec(v_x_2233_);
v_x_2231_ = v_fn_2239_;
v_x_2232_ = v___x_2241_;
v_x_2233_ = v___x_2243_;
goto _start;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec(v_x_2233_);
v___x_2245_ = l_Lean_instInhabitedExpr;
v___x_2246_ = l_Lean_Meta_PProdN_mk(v_rlvl_2226_, v_prods_2227_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v___x_2248_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2228_, v_x_2231_);
lean_dec_ref(v_x_2231_);
if (lean_obj_tag(v___x_2248_) == 1)
{
lean_object* v_val_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec_ref(v_minor__type_2230_);
lean_dec_ref(v_motives_2228_);
v_val_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = lean_array_get_borrowed(v___x_2245_, v_fs_2229_, v_val_2249_);
lean_dec(v_val_2249_);
lean_inc(v_a_2247_);
v___x_2251_ = lean_array_push(v_x_2232_, v_a_2247_);
lean_inc(v___x_2250_);
v___x_2252_ = l_Lean_mkAppN(v___x_2250_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = l_Lean_Meta_mkPProdMk(v___x_2252_, v_a_2247_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec(v___x_2248_);
lean_dec(v_a_2247_);
lean_dec_ref(v_x_2232_);
v___x_2254_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2255_ = l_Lean_MessageData_ofExpr(v_minor__type_2230_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = lean_array_to_list(v_motives_2228_);
v___x_2260_ = lean_box(0);
v___x_2261_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2259_, v___x_2260_);
v___x_2262_ = l_Lean_MessageData_ofList(v___x_2261_);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2258_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2263_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2264_;
}
}
else
{
lean_dec_ref(v_x_2232_);
lean_dec_ref(v_x_2231_);
lean_dec_ref(v_minor__type_2230_);
lean_dec_ref(v_motives_2228_);
return v___x_2246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2265_, lean_object* v_prods_2266_, lean_object* v_motives_2267_, lean_object* v_fs_2268_, lean_object* v_minor__type_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2265_, v_prods_2266_, v_motives_2267_, v_fs_2268_, v_minor__type_2269_, v_x_2270_, v_x_2271_, v_x_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_fs_2268_);
return v_res_2278_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2279_; lean_object* v_dummy_2280_; 
v___x_2279_ = lean_box(0);
v_dummy_2280_ = l_Lean_Expr_sort___override(v___x_2279_);
return v_dummy_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2281_, lean_object* v_head_2282_, lean_object* v_belows_2283_, lean_object* v_prods_2284_, lean_object* v_rlvl_2285_, lean_object* v_fs_2286_, lean_object* v_minor__type_2287_, lean_object* v_tail_2288_, lean_object* v_arg__args_2289_, lean_object* v_arg__type_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2281_, v_head_2282_, v_belows_2283_, v_prods_2284_, v_rlvl_2285_, v_fs_2286_, v_minor__type_2287_, v_tail_2288_, v_arg__args_2289_, v_arg__type_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_arg__args_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2297_, lean_object* v_motives_2298_, lean_object* v_belows_2299_, lean_object* v_fs_2300_, lean_object* v_minor__type_2301_, lean_object* v_prods_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
if (lean_obj_tag(v_a_2303_) == 0)
{
lean_object* v_dummy_2309_; lean_object* v_nargs_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v_belows_2299_);
v_dummy_2309_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2310_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2301_);
lean_inc(v_nargs_2310_);
v___x_2311_ = lean_mk_array(v_nargs_2310_, v_dummy_2309_);
v___x_2312_ = lean_unsigned_to_nat(1u);
v___x_2313_ = lean_nat_sub(v_nargs_2310_, v___x_2312_);
lean_dec(v_nargs_2310_);
lean_inc_ref(v_minor__type_2301_);
v___x_2314_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2297_, v_prods_2302_, v_motives_2298_, v_fs_2300_, v_minor__type_2301_, v_minor__type_2301_, v___x_2311_, v___x_2313_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec_ref(v_fs_2300_);
return v___x_2314_;
}
else
{
lean_object* v_head_2315_; lean_object* v_tail_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; 
v_head_2315_ = lean_ctor_get(v_a_2303_, 0);
lean_inc_n(v_head_2315_, 2);
v_tail_2316_ = lean_ctor_get(v_a_2303_, 1);
lean_inc(v_tail_2316_);
lean_dec_ref_known(v_a_2303_, 2);
v___f_2317_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2317_, 0, v_motives_2298_);
lean_closure_set(v___f_2317_, 1, v_head_2315_);
lean_closure_set(v___f_2317_, 2, v_belows_2299_);
lean_closure_set(v___f_2317_, 3, v_prods_2302_);
lean_closure_set(v___f_2317_, 4, v_rlvl_2297_);
lean_closure_set(v___f_2317_, 5, v_fs_2300_);
lean_closure_set(v___f_2317_, 6, v_minor__type_2301_);
lean_closure_set(v___f_2317_, 7, v_tail_2316_);
lean_inc(v_a_2307_);
lean_inc_ref(v_a_2306_);
lean_inc(v_a_2305_);
lean_inc_ref(v_a_2304_);
v___x_2318_ = lean_infer_type(v_head_2315_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = 0;
v___x_2321_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2319_, v___f_2317_, v___x_2320_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
return v___x_2321_;
}
else
{
lean_dec_ref(v___f_2317_);
return v___x_2318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2322_, lean_object* v_rlvl_2323_, lean_object* v_motives_2324_, lean_object* v_belows_2325_, lean_object* v_fs_2326_, lean_object* v_minor__type_2327_, lean_object* v_tail_2328_, uint8_t v___x_2329_, uint8_t v___x_2330_, uint8_t v___x_2331_, lean_object* v_arg_x27_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
lean_inc_ref(v_arg_x27_2332_);
v___x_2338_ = lean_array_push(v_prods_2322_, v_arg_x27_2332_);
v___x_2339_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2323_, v_motives_2324_, v_belows_2325_, v_fs_2326_, v_minor__type_2327_, v___x_2338_, v_tail_2328_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_mk_empty_array_with_capacity(v___x_2341_);
v___x_2343_ = lean_array_push(v___x_2342_, v_arg_x27_2332_);
v___x_2344_ = l_Lean_Meta_mkLambdaFVars(v___x_2343_, v_a_2340_, v___x_2329_, v___x_2330_, v___x_2329_, v___x_2330_, v___x_2331_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec_ref(v___x_2343_);
return v___x_2344_;
}
else
{
lean_dec_ref(v_arg_x27_2332_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2345_, lean_object* v_rlvl_2346_, lean_object* v_motives_2347_, lean_object* v_belows_2348_, lean_object* v_fs_2349_, lean_object* v_minor__type_2350_, lean_object* v_tail_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v___x_2354_, lean_object* v_arg_x27_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
uint8_t v___x_1689__boxed_2361_; uint8_t v___x_1690__boxed_2362_; uint8_t v___x_1691__boxed_2363_; lean_object* v_res_2364_; 
v___x_1689__boxed_2361_ = lean_unbox(v___x_2352_);
v___x_1690__boxed_2362_ = lean_unbox(v___x_2353_);
v___x_1691__boxed_2363_ = lean_unbox(v___x_2354_);
v_res_2364_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2345_, v_rlvl_2346_, v_motives_2347_, v_belows_2348_, v_fs_2349_, v_minor__type_2350_, v_tail_2351_, v___x_1689__boxed_2361_, v___x_1690__boxed_2362_, v___x_1691__boxed_2363_, v_arg_x27_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2365_, lean_object* v_head_2366_, lean_object* v_belows_2367_, lean_object* v_arg__type_2368_, lean_object* v_prods_2369_, lean_object* v_rlvl_2370_, lean_object* v_fs_2371_, lean_object* v_minor__type_2372_, lean_object* v_tail_2373_, lean_object* v_arg__args_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
if (lean_obj_tag(v_x_2375_) == 5)
{
lean_object* v_fn_2383_; lean_object* v_arg_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v_fn_2383_ = lean_ctor_get(v_x_2375_, 0);
lean_inc_ref(v_fn_2383_);
v_arg_2384_ = lean_ctor_get(v_x_2375_, 1);
lean_inc_ref(v_arg_2384_);
lean_dec_ref_known(v_x_2375_, 2);
v___x_2385_ = lean_array_set(v_x_2376_, v_x_2377_, v_arg_2384_);
v___x_2386_ = lean_unsigned_to_nat(1u);
v___x_2387_ = lean_nat_sub(v_x_2377_, v___x_2386_);
lean_dec(v_x_2377_);
v_x_2375_ = v_fn_2383_;
v_x_2376_ = v___x_2385_;
v_x_2377_ = v___x_2387_;
goto _start;
}
else
{
lean_object* v___x_2389_; 
lean_dec(v_x_2377_);
v___x_2389_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2365_, v_x_2375_);
lean_dec_ref(v_x_2375_);
if (lean_obj_tag(v___x_2389_) == 1)
{
lean_object* v_val_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_val_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_val_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_instInhabitedExpr;
v___x_2392_ = l_Lean_Expr_fvarId_x21(v_head_2366_);
lean_dec_ref(v_head_2366_);
v___x_2393_ = l_Lean_FVarId_getUserName___redArg(v___x_2392_, v___y_2378_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = lean_array_get_borrowed(v___x_2391_, v_belows_2367_, v_val_2390_);
lean_dec(v_val_2390_);
lean_inc(v___x_2395_);
v___x_2396_ = l_Lean_mkAppN(v___x_2395_, v_x_2376_);
lean_dec_ref(v_x_2376_);
v___x_2397_ = l_Lean_Meta_mkPProd(v_arg__type_2368_, v___x_2396_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; uint8_t v___x_2399_; uint8_t v___x_2400_; uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
lean_dec_ref_known(v___x_2397_, 1);
v___x_2399_ = 0;
v___x_2400_ = 1;
v___x_2401_ = 1;
v___x_2402_ = lean_box(v___x_2399_);
v___x_2403_ = lean_box(v___x_2400_);
v___x_2404_ = lean_box(v___x_2401_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2405_, 0, v_prods_2369_);
lean_closure_set(v___f_2405_, 1, v_rlvl_2370_);
lean_closure_set(v___f_2405_, 2, v_motives_2365_);
lean_closure_set(v___f_2405_, 3, v_belows_2367_);
lean_closure_set(v___f_2405_, 4, v_fs_2371_);
lean_closure_set(v___f_2405_, 5, v_minor__type_2372_);
lean_closure_set(v___f_2405_, 6, v_tail_2373_);
lean_closure_set(v___f_2405_, 7, v___x_2402_);
lean_closure_set(v___f_2405_, 8, v___x_2403_);
lean_closure_set(v___f_2405_, 9, v___x_2404_);
v___x_2406_ = l_Lean_Meta_mkForallFVars(v_arg__args_2374_, v_a_2398_, v___x_2399_, v___x_2400_, v___x_2400_, v___x_2401_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2394_, v_a_2407_, v___f_2405_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
return v___x_2408_;
}
else
{
lean_dec_ref(v___f_2405_);
lean_dec(v_a_2394_);
return v___x_2406_;
}
}
else
{
lean_dec(v_a_2394_);
lean_dec(v_tail_2373_);
lean_dec_ref(v_minor__type_2372_);
lean_dec_ref(v_fs_2371_);
lean_dec(v_rlvl_2370_);
lean_dec_ref(v_prods_2369_);
lean_dec_ref(v_belows_2367_);
lean_dec_ref(v_motives_2365_);
return v___x_2397_;
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_val_2390_);
lean_dec_ref(v_x_2376_);
lean_dec(v_tail_2373_);
lean_dec_ref(v_minor__type_2372_);
lean_dec_ref(v_fs_2371_);
lean_dec(v_rlvl_2370_);
lean_dec_ref(v_prods_2369_);
lean_dec_ref(v_arg__type_2368_);
lean_dec_ref(v_belows_2367_);
lean_dec_ref(v_motives_2365_);
v_a_2409_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2393_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2393_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v___x_2417_; 
lean_dec(v___x_2389_);
lean_dec_ref(v_x_2376_);
lean_dec_ref(v_arg__type_2368_);
v___x_2417_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2370_, v_motives_2365_, v_belows_2367_, v_fs_2371_, v_minor__type_2372_, v_prods_2369_, v_tail_2373_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; uint8_t v___x_2422_; uint8_t v___x_2423_; uint8_t v___x_2424_; lean_object* v___x_2425_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = lean_unsigned_to_nat(1u);
v___x_2420_ = lean_mk_empty_array_with_capacity(v___x_2419_);
v___x_2421_ = lean_array_push(v___x_2420_, v_head_2366_);
v___x_2422_ = 0;
v___x_2423_ = 1;
v___x_2424_ = 1;
v___x_2425_ = l_Lean_Meta_mkLambdaFVars(v___x_2421_, v_a_2418_, v___x_2422_, v___x_2423_, v___x_2422_, v___x_2423_, v___x_2424_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec_ref(v___x_2421_);
return v___x_2425_;
}
else
{
lean_dec_ref(v_head_2366_);
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2426_, lean_object* v_head_2427_, lean_object* v_belows_2428_, lean_object* v_prods_2429_, lean_object* v_rlvl_2430_, lean_object* v_fs_2431_, lean_object* v_minor__type_2432_, lean_object* v_tail_2433_, lean_object* v_arg__args_2434_, lean_object* v_arg__type_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_dummy_2441_; lean_object* v_nargs_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_dummy_2441_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2442_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2435_);
lean_inc(v_nargs_2442_);
v___x_2443_ = lean_mk_array(v_nargs_2442_, v_dummy_2441_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_sub(v_nargs_2442_, v___x_2444_);
lean_dec(v_nargs_2442_);
lean_inc_ref(v_arg__type_2435_);
v___x_2446_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2426_, v_head_2427_, v_belows_2428_, v_arg__type_2435_, v_prods_2429_, v_rlvl_2430_, v_fs_2431_, v_minor__type_2432_, v_tail_2433_, v_arg__args_2434_, v_arg__type_2435_, v___x_2443_, v___x_2445_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2447_, lean_object* v_motives_2448_, lean_object* v_belows_2449_, lean_object* v_fs_2450_, lean_object* v_minor__type_2451_, lean_object* v_prods_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2447_, v_motives_2448_, v_belows_2449_, v_fs_2450_, v_minor__type_2451_, v_prods_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2460_ = _args[0];
lean_object* v_head_2461_ = _args[1];
lean_object* v_belows_2462_ = _args[2];
lean_object* v_arg__type_2463_ = _args[3];
lean_object* v_prods_2464_ = _args[4];
lean_object* v_rlvl_2465_ = _args[5];
lean_object* v_fs_2466_ = _args[6];
lean_object* v_minor__type_2467_ = _args[7];
lean_object* v_tail_2468_ = _args[8];
lean_object* v_arg__args_2469_ = _args[9];
lean_object* v_x_2470_ = _args[10];
lean_object* v_x_2471_ = _args[11];
lean_object* v_x_2472_ = _args[12];
lean_object* v___y_2473_ = _args[13];
lean_object* v___y_2474_ = _args[14];
lean_object* v___y_2475_ = _args[15];
lean_object* v___y_2476_ = _args[16];
lean_object* v___y_2477_ = _args[17];
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2460_, v_head_2461_, v_belows_2462_, v_arg__type_2463_, v_prods_2464_, v_rlvl_2465_, v_fs_2466_, v_minor__type_2467_, v_tail_2468_, v_arg__args_2469_, v_x_2470_, v_x_2471_, v_x_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v_arg__args_2469_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2479_, lean_object* v_motives_2480_, lean_object* v_belows_2481_, lean_object* v_fs_2482_, lean_object* v_minor__args_2483_, lean_object* v_minor__type_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2491_ = lean_array_to_list(v_minor__args_2483_);
v___x_2492_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2479_, v_motives_2480_, v_belows_2481_, v_fs_2482_, v_minor__type_2484_, v___x_2490_, v___x_2491_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2493_, lean_object* v_motives_2494_, lean_object* v_belows_2495_, lean_object* v_fs_2496_, lean_object* v_minor__args_2497_, lean_object* v_minor__type_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2493_, v_motives_2494_, v_belows_2495_, v_fs_2496_, v_minor__args_2497_, v_minor__type_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2505_, lean_object* v_motives_2506_, lean_object* v_belows_2507_, lean_object* v_fs_2508_, lean_object* v_minorType_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v___f_2515_; uint8_t v___x_2516_; lean_object* v___x_2517_; 
v___f_2515_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2515_, 0, v_rlvl_2505_);
lean_closure_set(v___f_2515_, 1, v_motives_2506_);
lean_closure_set(v___f_2515_, 2, v_belows_2507_);
lean_closure_set(v___f_2515_, 3, v_fs_2508_);
v___x_2516_ = 0;
v___x_2517_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2509_, v___f_2515_, v___x_2516_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2518_, lean_object* v_motives_2519_, lean_object* v_belows_2520_, lean_object* v_fs_2521_, lean_object* v_minorType_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2518_, v_motives_2519_, v_belows_2520_, v_fs_2521_, v_minorType_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___f_2535_; lean_object* v___x_27356__overap_2536_; lean_object* v___x_2537_; 
v___f_2535_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27356__overap_2536_ = lean_panic_fn_borrowed(v___f_2535_, v_msg_2529_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
v___x_2537_ = lean_apply_5(v___x_27356__overap_2536_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2545_, lean_object* v___y_2546_){
_start:
{
uint8_t v___x_2548_; 
v___x_2548_ = l_Lean_Expr_hasMVar(v_e_2545_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v_e_2545_);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; lean_object* v_mctx_2551_; lean_object* v___x_2552_; lean_object* v_fst_2553_; lean_object* v_snd_2554_; lean_object* v___x_2555_; lean_object* v_cache_2556_; lean_object* v_zetaDeltaFVarIds_2557_; lean_object* v_postponed_2558_; lean_object* v_diag_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2568_; 
v___x_2550_ = lean_st_ref_get(v___y_2546_);
v_mctx_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc_ref(v_mctx_2551_);
lean_dec(v___x_2550_);
v___x_2552_ = l_Lean_instantiateMVarsCore(v_mctx_2551_, v_e_2545_);
v_fst_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_fst_2553_);
v_snd_2554_ = lean_ctor_get(v___x_2552_, 1);
lean_inc(v_snd_2554_);
lean_dec_ref(v___x_2552_);
v___x_2555_ = lean_st_ref_take(v___y_2546_);
v_cache_2556_ = lean_ctor_get(v___x_2555_, 1);
v_zetaDeltaFVarIds_2557_ = lean_ctor_get(v___x_2555_, 2);
v_postponed_2558_ = lean_ctor_get(v___x_2555_, 3);
v_diag_2559_ = lean_ctor_get(v___x_2555_, 4);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2569_);
v___x_2561_ = v___x_2555_;
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_diag_2559_);
lean_inc(v_postponed_2558_);
lean_inc(v_zetaDeltaFVarIds_2557_);
lean_inc(v_cache_2556_);
lean_dec(v___x_2555_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2568_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v_snd_2554_);
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_snd_2554_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_cache_2556_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v_zetaDeltaFVarIds_2557_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v_postponed_2558_);
lean_ctor_set(v_reuseFailAlloc_2567_, 4, v_diag_2559_);
v___x_2564_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_st_ref_put(v___y_2546_, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v_fst_2553_);
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2570_, v___y_2571_);
lean_dec(v___y_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2574_, v___y_2576_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v_env_2592_; lean_object* v_toConstantVal_2593_; lean_object* v_value_2594_; lean_object* v_all_2595_; uint8_t v___y_2597_; lean_object* v_type_2605_; uint8_t v___x_2606_; 
v___x_2591_ = lean_st_ref_get(v___y_2589_);
v_env_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc_ref_n(v_env_2592_, 2);
lean_dec(v___x_2591_);
v_toConstantVal_2593_ = lean_ctor_get(v_thm_2588_, 0);
v_value_2594_ = lean_ctor_get(v_thm_2588_, 1);
v_all_2595_ = lean_ctor_get(v_thm_2588_, 2);
v_type_2605_ = lean_ctor_get(v_toConstantVal_2593_, 2);
v___x_2606_ = l_Lean_Environment_hasUnsafe(v_env_2592_, v_type_2605_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
v___x_2607_ = l_Lean_Environment_hasUnsafe(v_env_2592_, v_value_2594_);
v___y_2597_ = v___x_2607_;
goto v___jp_2596_;
}
else
{
lean_dec_ref(v_env_2592_);
v___y_2597_ = v___x_2606_;
goto v___jp_2596_;
}
v___jp_2596_:
{
if (v___y_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_thm_2588_);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
else
{
lean_object* v___x_2600_; uint8_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_inc(v_all_2595_);
lean_inc_ref(v_value_2594_);
lean_inc_ref(v_toConstantVal_2593_);
lean_dec_ref(v_thm_2588_);
v___x_2600_ = lean_box(0);
v___x_2601_ = 0;
v___x_2602_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2602_, 0, v_toConstantVal_2593_);
lean_ctor_set(v___x_2602_, 1, v_value_2594_);
lean_ctor_set(v___x_2602_, 2, v___x_2600_);
lean_ctor_set(v___x_2602_, 3, v_all_2595_);
lean_ctor_set_uint8(v___x_2602_, sizeof(void*)*4, v___x_2601_);
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2608_, v___y_2609_);
lean_dec(v___y_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2612_, v___y_2616_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v_all_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v_x_2634_){
_start:
{
lean_object* v___y_2636_; lean_object* v___x_2640_; uint8_t v___x_2641_; 
v___x_2640_ = lean_array_get_size(v_all_2630_);
v___x_2641_ = lean_nat_dec_lt(v_x_2634_, v___x_2640_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2642_ = lean_array_get_borrowed(v___x_2631_, v_all_2630_, v___x_2632_);
v___x_2643_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2644_ = lean_nat_sub(v_x_2634_, v___x_2640_);
v___x_2645_ = lean_nat_add(v___x_2644_, v___x_2633_);
lean_dec(v___x_2644_);
v___x_2646_ = l_Nat_reprFast(v___x_2645_);
v___x_2647_ = lean_string_append(v___x_2643_, v___x_2646_);
lean_dec_ref(v___x_2646_);
lean_inc(v___x_2642_);
v___x_2648_ = l_Lean_Name_str___override(v___x_2642_, v___x_2647_);
v___y_2636_ = v___x_2648_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_array_fget_borrowed(v_all_2630_, v_x_2634_);
lean_inc(v___x_2649_);
v___x_2650_ = l_Lean_mkBelowName(v___x_2649_);
v___y_2636_ = v___x_2650_;
goto v___jp_2635_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2637_ = l_Lean_Expr_const___override(v___y_2636_, v___x_2627_);
v___x_2638_ = l_Array_append___redArg(v___x_2628_, v___x_2629_);
v___x_2639_ = l_Lean_mkAppN(v___x_2637_, v___x_2638_);
lean_dec_ref(v___x_2638_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2651_, lean_object* v___x_2652_, lean_object* v___x_2653_, lean_object* v_all_2654_, lean_object* v___x_2655_, lean_object* v___x_2656_, lean_object* v___x_2657_, lean_object* v_x_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2651_, v___x_2652_, v___x_2653_, v_all_2654_, v___x_2655_, v___x_2656_, v___x_2657_, v_x_2658_);
lean_dec(v_x_2658_);
lean_dec(v___x_2657_);
lean_dec(v___x_2656_);
lean_dec(v___x_2655_);
lean_dec_ref(v_all_2654_);
lean_dec_ref(v___x_2653_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2660_, lean_object* v___x_2661_, lean_object* v___x_2662_, lean_object* v_fs_2663_, lean_object* v_as_2664_, size_t v_sz_2665_, size_t v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v___x_2673_; 
v___x_2673_ = lean_usize_dec_lt(v_i_2666_, v_sz_2665_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref(v_fs_2663_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2661_);
lean_dec(v___x_2660_);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v_b_2667_);
return v___x_2674_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2676_; 
v_a_2675_ = lean_array_uget_borrowed(v_as_2664_, v_i_2666_);
lean_inc(v___y_2671_);
lean_inc_ref(v___y_2670_);
lean_inc(v___y_2669_);
lean_inc_ref(v___y_2668_);
lean_inc(v_a_2675_);
v___x_2676_ = lean_infer_type(v_a_2675_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
lean_inc_ref(v_fs_2663_);
lean_inc_ref(v___x_2662_);
lean_inc_ref(v___x_2661_);
lean_inc(v___x_2660_);
v___x_2678_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2660_, v___x_2661_, v___x_2662_, v_fs_2663_, v_a_2677_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; size_t v___x_2681_; size_t v___x_2682_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v___x_2680_ = l_Lean_Expr_app___override(v_b_2667_, v_a_2679_);
v___x_2681_ = ((size_t)1ULL);
v___x_2682_ = lean_usize_add(v_i_2666_, v___x_2681_);
v_i_2666_ = v___x_2682_;
v_b_2667_ = v___x_2680_;
goto _start;
}
else
{
lean_dec_ref(v_b_2667_);
lean_dec_ref(v_fs_2663_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2661_);
lean_dec(v___x_2660_);
return v___x_2678_;
}
}
else
{
lean_dec_ref(v_b_2667_);
lean_dec_ref(v_fs_2663_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2661_);
lean_dec(v___x_2660_);
return v___x_2676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v_fs_2687_, lean_object* v_as_2688_, lean_object* v_sz_2689_, lean_object* v_i_2690_, lean_object* v_b_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
size_t v_sz_boxed_2697_; size_t v_i_boxed_2698_; lean_object* v_res_2699_; 
v_sz_boxed_2697_ = lean_unbox_usize(v_sz_2689_);
lean_dec(v_sz_2689_);
v_i_boxed_2698_ = lean_unbox_usize(v_i_2690_);
lean_dec(v_i_2690_);
v_res_2699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2684_, v___x_2685_, v___x_2686_, v_fs_2687_, v_as_2688_, v_sz_boxed_2697_, v_i_boxed_2698_, v_b_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec_ref(v_as_2688_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2700_, lean_object* v___x_2701_, uint8_t v___x_2702_, lean_object* v_targs_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = l_Lean_mkAppN(v_a_2700_, v_targs_2703_);
v___x_2711_ = l_Lean_mkAppN(v___x_2701_, v_targs_2703_);
v___x_2712_ = l_Lean_Meta_mkPProd(v___x_2710_, v___x_2711_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; uint8_t v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = 0;
v___x_2715_ = 1;
v___x_2716_ = l_Lean_Meta_mkLambdaFVars(v_targs_2703_, v_a_2713_, v___x_2714_, v___x_2702_, v___x_2714_, v___x_2702_, v___x_2715_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
return v___x_2716_;
}
else
{
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2717_, lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v_targs_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
uint8_t v___x_30628__boxed_2727_; lean_object* v_res_2728_; 
v___x_30628__boxed_2727_ = lean_unbox(v___x_2719_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2717_, v___x_2718_, v___x_30628__boxed_2727_, v_targs_2720_, v_x_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_x_2721_);
lean_dec_ref(v_targs_2720_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2729_, lean_object* v___x_2730_, lean_object* v_as_2731_, size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_usize_dec_lt(v_i_2733_, v_sz_2732_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_b_2734_);
return v___x_2741_;
}
else
{
lean_object* v_snd_2742_; lean_object* v_fst_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2800_; 
v_snd_2742_ = lean_ctor_get(v_b_2734_, 1);
v_fst_2743_ = lean_ctor_get(v_b_2734_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_b_2734_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2745_ = v_b_2734_;
v_isShared_2746_ = v_isSharedCheck_2800_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snd_2742_);
lean_inc(v_fst_2743_);
lean_dec(v_b_2734_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2800_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v_array_2747_; lean_object* v_start_2748_; lean_object* v_stop_2749_; uint8_t v___x_2750_; 
v_array_2747_ = lean_ctor_get(v_snd_2742_, 0);
v_start_2748_ = lean_ctor_get(v_snd_2742_, 1);
v_stop_2749_ = lean_ctor_get(v_snd_2742_, 2);
v___x_2750_ = lean_nat_dec_lt(v_start_2748_, v_stop_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2752_; 
if (v_isShared_2746_ == 0)
{
v___x_2752_ = v___x_2745_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_fst_2743_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_snd_2742_);
v___x_2752_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
return v___x_2753_;
}
}
else
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2796_; 
lean_inc(v_stop_2749_);
lean_inc(v_start_2748_);
lean_inc_ref(v_array_2747_);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_snd_2742_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; 
v_unused_2797_ = lean_ctor_get(v_snd_2742_, 2);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_snd_2742_, 1);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_snd_2742_, 0);
lean_dec(v_unused_2799_);
v___x_2756_ = v_snd_2742_;
v_isShared_2757_ = v_isSharedCheck_2796_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v_snd_2742_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2796_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
uint8_t v___x_2758_; lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___f_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2758_ = lean_nat_dec_lt(v___x_2729_, v___x_2730_);
v_a_2759_ = lean_array_uget_borrowed(v_as_2731_, v_i_2733_);
v___x_2760_ = lean_array_fget_borrowed(v_array_2747_, v_start_2748_);
v___x_2761_ = lean_box(v___x_2758_);
lean_inc(v___x_2760_);
lean_inc(v_a_2759_);
v___f_2762_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2762_, 0, v_a_2759_);
lean_closure_set(v___f_2762_, 1, v___x_2760_);
lean_closure_set(v___f_2762_, 2, v___x_2761_);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_nat_add(v_start_2748_, v___x_2763_);
lean_dec(v_start_2748_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v___x_2764_);
v___x_2766_ = v___x_2756_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_array_2747_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_stop_2749_);
v___x_2766_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; 
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v_a_2759_);
v___x_2767_ = lean_infer_type(v_a_2759_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = 0;
v___x_2770_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2768_, v___f_2762_, v___x_2769_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = l_Lean_Expr_app___override(v_fst_2743_, v_a_2771_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 1, v___x_2766_);
lean_ctor_set(v___x_2745_, 0, v___x_2772_);
v___x_2774_ = v___x_2745_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2766_);
v___x_2774_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
size_t v___x_2775_; size_t v___x_2776_; 
v___x_2775_ = ((size_t)1ULL);
v___x_2776_ = lean_usize_add(v_i_2733_, v___x_2775_);
v_i_2733_ = v___x_2776_;
v_b_2734_ = v___x_2774_;
goto _start;
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v___x_2766_);
lean_del_object(v___x_2745_);
lean_dec(v_fst_2743_);
v_a_2779_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2770_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2770_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v___x_2766_);
lean_dec_ref(v___f_2762_);
lean_del_object(v___x_2745_);
lean_dec(v_fst_2743_);
v_a_2787_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2767_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2767_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v_as_2803_, lean_object* v_sz_2804_, lean_object* v_i_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_sz_boxed_2812_; size_t v_i_boxed_2813_; lean_object* v_res_2814_; 
v_sz_boxed_2812_ = lean_unbox_usize(v_sz_2804_);
lean_dec(v_sz_2804_);
v_i_boxed_2813_ = lean_unbox_usize(v_i_2805_);
lean_dec(v_i_2805_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2801_, v___x_2802_, v_as_2803_, v_sz_boxed_2812_, v_i_boxed_2813_, v_b_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_as_2803_);
lean_dec(v___x_2802_);
lean_dec(v___x_2801_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2815_, size_t v_sz_2816_, size_t v_i_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_usize_dec_lt(v_i_2817_, v_sz_2816_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v_b_2818_);
return v___x_2825_;
}
else
{
lean_object* v_a_2826_; lean_object* v_toInductionSubgoal_2827_; lean_object* v_mvarId_2828_; uint8_t v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_a_2826_ = lean_array_uget_borrowed(v_as_2815_, v_i_2817_);
v_toInductionSubgoal_2827_ = lean_ctor_get(v_a_2826_, 0);
v_mvarId_2828_ = lean_ctor_get(v_toInductionSubgoal_2827_, 0);
v___x_2829_ = 0;
v___x_2830_ = lean_box(0);
lean_inc(v_mvarId_2828_);
v___x_2831_ = l_Lean_MVarId_refl(v_mvarId_2828_, v___x_2829_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2831_) == 0)
{
size_t v___x_2832_; size_t v___x_2833_; 
lean_dec_ref_known(v___x_2831_, 1);
v___x_2832_ = ((size_t)1ULL);
v___x_2833_ = lean_usize_add(v_i_2817_, v___x_2832_);
v_i_2817_ = v___x_2833_;
v_b_2818_ = v___x_2830_;
goto _start;
}
else
{
return v___x_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2835_, lean_object* v_sz_2836_, lean_object* v_i_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
size_t v_sz_boxed_2844_; size_t v_i_boxed_2845_; lean_object* v_res_2846_; 
v_sz_boxed_2844_ = lean_unbox_usize(v_sz_2836_);
lean_dec(v_sz_2836_);
v_i_boxed_2845_ = lean_unbox_usize(v_i_2837_);
lean_dec(v_i_2837_);
v_res_2846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2835_, v_sz_boxed_2844_, v_i_boxed_2845_, v_b_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v_as_2835_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2847_, lean_object* v_tail_2848_, lean_object* v_recName_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v_val_2861_, uint8_t v___x_2862_, lean_object* v_brecOnGoName_2863_, lean_object* v_levelParams_2864_, lean_object* v___x_2865_, lean_object* v_brecOnName_2866_, lean_object* v___x_2867_, lean_object* v_brecOnEqName_2868_, lean_object* v_fs_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; size_t v_sz_2879_; size_t v___x_2880_; lean_object* v___x_2881_; 
lean_inc(v___x_2847_);
v___x_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2847_);
lean_ctor_set(v___x_2875_, 1, v_tail_2848_);
v___x_2876_ = l_Lean_Expr_const___override(v_recName_2849_, v___x_2875_);
v___x_2877_ = l_Lean_mkAppN(v___x_2876_, v___x_2850_);
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v___x_2851_);
v_sz_2879_ = lean_array_size(v___x_2852_);
v___x_2880_ = ((size_t)0ULL);
v___x_2881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2853_, v___x_2854_, v___x_2852_, v_sz_2879_, v___x_2880_, v___x_2878_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v_fst_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_3248_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v_fst_2883_ = lean_ctor_get(v_a_2882_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_a_2882_);
if (v_isSharedCheck_3248_ == 0)
{
lean_object* v_unused_3249_; 
v_unused_3249_ = lean_ctor_get(v_a_2882_, 1);
lean_dec(v_unused_3249_);
v___x_2885_ = v_a_2882_;
v_isShared_2886_ = v_isSharedCheck_3248_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_fst_2883_);
lean_dec(v_a_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_3248_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
size_t v_sz_2887_; lean_object* v___x_2888_; 
v_sz_2887_ = lean_array_size(v___x_2855_);
lean_inc_ref(v_fs_2869_);
lean_inc_ref(v___x_2856_);
lean_inc_ref(v___x_2852_);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2847_, v___x_2852_, v___x_2856_, v_fs_2869_, v___x_2855_, v_sz_2887_, v___x_2880_, v_fst_2883_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = l_Lean_mkAppN(v_a_2889_, v___x_2857_);
lean_inc_ref_n(v___x_2858_, 3);
v___x_2891_ = l_Lean_Expr_app___override(v___x_2890_, v___x_2858_);
v___x_2892_ = l_Array_append___redArg(v___x_2850_, v___x_2852_);
v___x_2893_ = l_Array_append___redArg(v___x_2892_, v___x_2857_);
v___x_2894_ = lean_mk_empty_array_with_capacity(v___x_2859_);
v___x_2895_ = lean_array_push(v___x_2894_, v___x_2858_);
v___x_2896_ = l_Array_append___redArg(v___x_2893_, v___x_2895_);
lean_dec_ref(v___x_2895_);
v___x_2897_ = l_Array_append___redArg(v___x_2896_, v_fs_2869_);
v___x_2898_ = lean_array_get(v___x_2860_, v___x_2852_, v_val_2861_);
lean_dec_ref(v___x_2852_);
v___x_2899_ = lean_array_push(v___x_2857_, v___x_2858_);
v___x_2900_ = l_Lean_mkAppN(v___x_2898_, v___x_2899_);
v___x_2901_ = lean_array_get(v___x_2860_, v___x_2856_, v_val_2861_);
lean_dec_ref(v___x_2856_);
v___x_2902_ = l_Lean_mkAppN(v___x_2901_, v___x_2899_);
lean_inc_ref(v___x_2900_);
v___x_2903_ = l_Lean_Meta_mkPProd(v___x_2900_, v___x_2902_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; uint8_t v___x_2905_; uint8_t v___x_2906_; lean_object* v___x_2907_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = 0;
v___x_2906_ = 1;
v___x_2907_ = l_Lean_Meta_mkForallFVars(v___x_2897_, v_a_2904_, v___x_2905_, v___x_2862_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v___x_2909_ = l_Lean_Meta_mkLambdaFVars(v___x_2897_, v___x_2891_, v___x_2905_, v___x_2862_, v___x_2905_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3215_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v___x_2911_ = lean_box(1);
lean_inc(v_levelParams_2864_);
lean_inc(v_brecOnGoName_2863_);
v___x_2912_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2863_, v_levelParams_2864_, v_a_2908_, v_a_2910_, v___x_2911_, v___y_2873_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_3215_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3215_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
lean_inc(v_a_2913_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set_tag(v___x_2915_, 1);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_3214_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; 
v___x_2919_ = l_Lean_addDecl(v___x_2918_, v___x_2905_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_toConstantVal_2920_; lean_object* v_name_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref_known(v___x_2919_, 1);
v_toConstantVal_2920_ = lean_ctor_get(v_a_2913_, 0);
lean_inc_ref(v_toConstantVal_2920_);
lean_dec(v_a_2913_);
v_name_2921_ = lean_ctor_get(v_toConstantVal_2920_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_toConstantVal_2920_);
if (v_isSharedCheck_3211_ == 0)
{
lean_object* v_unused_3212_; lean_object* v_unused_3213_; 
v_unused_3212_ = lean_ctor_get(v_toConstantVal_2920_, 2);
lean_dec(v_unused_3212_);
v_unused_3213_ = lean_ctor_get(v_toConstantVal_2920_, 1);
lean_dec(v_unused_3213_);
v___x_2923_ = v_toConstantVal_2920_;
v_isShared_2924_ = v_isSharedCheck_3211_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_name_2921_);
lean_dec(v_toConstantVal_2920_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3211_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_env_2927_; lean_object* v_nextMacroScope_2928_; lean_object* v_ngen_2929_; lean_object* v_auxDeclNGen_2930_; lean_object* v_traceState_2931_; lean_object* v_recordedDeps_2932_; lean_object* v_messages_2933_; lean_object* v_infoState_2934_; lean_object* v_snapshotTasks_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3209_; 
lean_inc(v_name_2921_);
v___x_2925_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2921_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec_ref(v___x_2925_);
v___x_2926_ = lean_st_ref_take(v___y_2873_);
v_env_2927_ = lean_ctor_get(v___x_2926_, 0);
v_nextMacroScope_2928_ = lean_ctor_get(v___x_2926_, 1);
v_ngen_2929_ = lean_ctor_get(v___x_2926_, 2);
v_auxDeclNGen_2930_ = lean_ctor_get(v___x_2926_, 3);
v_traceState_2931_ = lean_ctor_get(v___x_2926_, 4);
v_recordedDeps_2932_ = lean_ctor_get(v___x_2926_, 6);
v_messages_2933_ = lean_ctor_get(v___x_2926_, 7);
v_infoState_2934_ = lean_ctor_get(v___x_2926_, 8);
v_snapshotTasks_2935_ = lean_ctor_get(v___x_2926_, 9);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v___x_2926_, 5);
lean_dec(v_unused_3210_);
v___x_2937_ = v___x_2926_;
v_isShared_2938_ = v_isSharedCheck_3209_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_snapshotTasks_2935_);
lean_inc(v_infoState_2934_);
lean_inc(v_messages_2933_);
lean_inc(v_recordedDeps_2932_);
lean_inc(v_traceState_2931_);
lean_inc(v_auxDeclNGen_2930_);
lean_inc(v_ngen_2929_);
lean_inc(v_nextMacroScope_2928_);
lean_inc(v_env_2927_);
lean_dec(v___x_2926_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3209_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2939_ = l_Lean_addProtected(v_env_2927_, v_name_2921_);
v___x_2940_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 5, v___x_2940_);
lean_ctor_set(v___x_2937_, 0, v___x_2939_);
v___x_2942_ = v___x_2937_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_nextMacroScope_2928_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v_ngen_2929_);
lean_ctor_set(v_reuseFailAlloc_3208_, 3, v_auxDeclNGen_2930_);
lean_ctor_set(v_reuseFailAlloc_3208_, 4, v_traceState_2931_);
lean_ctor_set(v_reuseFailAlloc_3208_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_3208_, 6, v_recordedDeps_2932_);
lean_ctor_set(v_reuseFailAlloc_3208_, 7, v_messages_2933_);
lean_ctor_set(v_reuseFailAlloc_3208_, 8, v_infoState_2934_);
lean_ctor_set(v_reuseFailAlloc_3208_, 9, v_snapshotTasks_2935_);
v___x_2942_ = v_reuseFailAlloc_3208_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_mctx_2945_; lean_object* v_zetaDeltaFVarIds_2946_; lean_object* v_postponed_2947_; lean_object* v_diag_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3206_; 
v___x_2943_ = lean_st_ref_put(v___y_2873_, v___x_2942_);
v___x_2944_ = lean_st_ref_take(v___y_2871_);
v_mctx_2945_ = lean_ctor_get(v___x_2944_, 0);
v_zetaDeltaFVarIds_2946_ = lean_ctor_get(v___x_2944_, 2);
v_postponed_2947_ = lean_ctor_get(v___x_2944_, 3);
v_diag_2948_ = lean_ctor_get(v___x_2944_, 4);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_2944_, 1);
lean_dec(v_unused_3207_);
v___x_2950_ = v___x_2944_;
v_isShared_2951_ = v_isSharedCheck_3206_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_diag_2948_);
lean_inc(v_postponed_2947_);
lean_inc(v_zetaDeltaFVarIds_2946_);
lean_inc(v_mctx_2945_);
lean_dec(v___x_2944_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3206_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2952_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 1, v___x_2952_);
v___x_2954_ = v___x_2950_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_mctx_2945_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_3205_, 2, v_zetaDeltaFVarIds_2946_);
lean_ctor_set(v_reuseFailAlloc_3205_, 3, v_postponed_2947_);
lean_ctor_set(v_reuseFailAlloc_3205_, 4, v_diag_2948_);
v___x_2954_ = v_reuseFailAlloc_3205_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = lean_st_ref_put(v___y_2871_, v___x_2954_);
lean_inc(v___x_2865_);
v___x_2956_ = l_Lean_Expr_const___override(v_brecOnGoName_2863_, v___x_2865_);
v___x_2957_ = l_Lean_mkAppN(v___x_2956_, v___x_2897_);
lean_inc_ref(v___x_2957_);
v___x_2958_ = l_Lean_Meta_mkPProdFstM(v___x_2957_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = l_Lean_Meta_mkLambdaFVars(v___x_2897_, v_a_2959_, v___x_2905_, v___x_2862_, v___x_2905_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; lean_object* v___x_2962_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
v___x_2962_ = l_Lean_Meta_mkForallFVars(v___x_2897_, v___x_2900_, v___x_2905_, v___x_2862_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3180_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
lean_inc(v_levelParams_2864_);
v___x_2964_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2866_, v_levelParams_2864_, v_a_2963_, v_a_2961_, v___x_2911_, v___y_2873_);
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_3180_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3180_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
lean_inc(v_a_2965_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 1);
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_3179_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Lean_addDecl(v___x_2970_, v___x_2905_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_toConstantVal_2972_; lean_object* v_name_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref_known(v___x_2971_, 1);
v_toConstantVal_2972_ = lean_ctor_get(v_a_2965_, 0);
lean_inc_ref(v_toConstantVal_2972_);
lean_dec(v_a_2965_);
v_name_2973_ = lean_ctor_get(v_toConstantVal_2972_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_toConstantVal_2972_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; 
v_unused_3177_ = lean_ctor_get(v_toConstantVal_2972_, 2);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_toConstantVal_2972_, 1);
lean_dec(v_unused_3178_);
v___x_2975_ = v_toConstantVal_2972_;
v_isShared_2976_ = v_isSharedCheck_3176_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_name_2973_);
lean_dec(v_toConstantVal_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3176_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_env_2979_; lean_object* v_nextMacroScope_2980_; lean_object* v_ngen_2981_; lean_object* v_auxDeclNGen_2982_; lean_object* v_traceState_2983_; lean_object* v_recordedDeps_2984_; lean_object* v_messages_2985_; lean_object* v_infoState_2986_; lean_object* v_snapshotTasks_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3174_; 
lean_inc(v_name_2973_);
v___x_2977_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2973_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec_ref(v___x_2977_);
v___x_2978_ = lean_st_ref_take(v___y_2873_);
v_env_2979_ = lean_ctor_get(v___x_2978_, 0);
v_nextMacroScope_2980_ = lean_ctor_get(v___x_2978_, 1);
v_ngen_2981_ = lean_ctor_get(v___x_2978_, 2);
v_auxDeclNGen_2982_ = lean_ctor_get(v___x_2978_, 3);
v_traceState_2983_ = lean_ctor_get(v___x_2978_, 4);
v_recordedDeps_2984_ = lean_ctor_get(v___x_2978_, 6);
v_messages_2985_ = lean_ctor_get(v___x_2978_, 7);
v_infoState_2986_ = lean_ctor_get(v___x_2978_, 8);
v_snapshotTasks_2987_ = lean_ctor_get(v___x_2978_, 9);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_2978_, 5);
lean_dec(v_unused_3175_);
v___x_2989_ = v___x_2978_;
v_isShared_2990_ = v_isSharedCheck_3174_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_snapshotTasks_2987_);
lean_inc(v_infoState_2986_);
lean_inc(v_messages_2985_);
lean_inc(v_recordedDeps_2984_);
lean_inc(v_traceState_2983_);
lean_inc(v_auxDeclNGen_2982_);
lean_inc(v_ngen_2981_);
lean_inc(v_nextMacroScope_2980_);
lean_inc(v_env_2979_);
lean_dec(v___x_2978_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3174_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_inc(v_name_2973_);
v___x_2991_ = l_Lean_markAuxRecursor(v_env_2979_, v_name_2973_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 5, v___x_2940_);
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_nextMacroScope_2980_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_ngen_2981_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_auxDeclNGen_2982_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_traceState_2983_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_3173_, 6, v_recordedDeps_2984_);
lean_ctor_set(v_reuseFailAlloc_3173_, 7, v_messages_2985_);
lean_ctor_set(v_reuseFailAlloc_3173_, 8, v_infoState_2986_);
lean_ctor_set(v_reuseFailAlloc_3173_, 9, v_snapshotTasks_2987_);
v___x_2993_ = v_reuseFailAlloc_3173_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v_mctx_2996_; lean_object* v_zetaDeltaFVarIds_2997_; lean_object* v_postponed_2998_; lean_object* v_diag_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3171_; 
v___x_2994_ = lean_st_ref_put(v___y_2873_, v___x_2993_);
v___x_2995_ = lean_st_ref_take(v___y_2871_);
v_mctx_2996_ = lean_ctor_get(v___x_2995_, 0);
v_zetaDeltaFVarIds_2997_ = lean_ctor_get(v___x_2995_, 2);
v_postponed_2998_ = lean_ctor_get(v___x_2995_, 3);
v_diag_2999_ = lean_ctor_get(v___x_2995_, 4);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v___x_2995_, 1);
lean_dec(v_unused_3172_);
v___x_3001_ = v___x_2995_;
v_isShared_3002_ = v_isSharedCheck_3171_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_diag_2999_);
lean_inc(v_postponed_2998_);
lean_inc(v_zetaDeltaFVarIds_2997_);
lean_inc(v_mctx_2996_);
lean_dec(v___x_2995_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3171_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_2952_);
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_mctx_2996_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_zetaDeltaFVarIds_2997_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_postponed_2998_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_diag_2999_);
v___x_3004_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v_env_3007_; lean_object* v_nextMacroScope_3008_; lean_object* v_ngen_3009_; lean_object* v_auxDeclNGen_3010_; lean_object* v_traceState_3011_; lean_object* v_recordedDeps_3012_; lean_object* v_messages_3013_; lean_object* v_infoState_3014_; lean_object* v_snapshotTasks_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3168_; 
v___x_3005_ = lean_st_ref_put(v___y_2871_, v___x_3004_);
v___x_3006_ = lean_st_ref_take(v___y_2873_);
v_env_3007_ = lean_ctor_get(v___x_3006_, 0);
v_nextMacroScope_3008_ = lean_ctor_get(v___x_3006_, 1);
v_ngen_3009_ = lean_ctor_get(v___x_3006_, 2);
v_auxDeclNGen_3010_ = lean_ctor_get(v___x_3006_, 3);
v_traceState_3011_ = lean_ctor_get(v___x_3006_, 4);
v_recordedDeps_3012_ = lean_ctor_get(v___x_3006_, 6);
v_messages_3013_ = lean_ctor_get(v___x_3006_, 7);
v_infoState_3014_ = lean_ctor_get(v___x_3006_, 8);
v_snapshotTasks_3015_ = lean_ctor_get(v___x_3006_, 9);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3006_, 5);
lean_dec(v_unused_3169_);
v___x_3017_ = v___x_3006_;
v_isShared_3018_ = v_isSharedCheck_3168_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_snapshotTasks_3015_);
lean_inc(v_infoState_3014_);
lean_inc(v_messages_3013_);
lean_inc(v_recordedDeps_3012_);
lean_inc(v_traceState_3011_);
lean_inc(v_auxDeclNGen_3010_);
lean_inc(v_ngen_3009_);
lean_inc(v_nextMacroScope_3008_);
lean_inc(v_env_3007_);
lean_dec(v___x_3006_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3168_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3019_; lean_object* v___x_3021_; 
lean_inc(v_name_2973_);
v___x_3019_ = l_Lean_addProtected(v_env_3007_, v_name_2973_);
if (v_isShared_3018_ == 0)
{
lean_ctor_set(v___x_3017_, 5, v___x_2940_);
lean_ctor_set(v___x_3017_, 0, v___x_3019_);
v___x_3021_ = v___x_3017_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v_nextMacroScope_3008_);
lean_ctor_set(v_reuseFailAlloc_3167_, 2, v_ngen_3009_);
lean_ctor_set(v_reuseFailAlloc_3167_, 3, v_auxDeclNGen_3010_);
lean_ctor_set(v_reuseFailAlloc_3167_, 4, v_traceState_3011_);
lean_ctor_set(v_reuseFailAlloc_3167_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_3167_, 6, v_recordedDeps_3012_);
lean_ctor_set(v_reuseFailAlloc_3167_, 7, v_messages_3013_);
lean_ctor_set(v_reuseFailAlloc_3167_, 8, v_infoState_3014_);
lean_ctor_set(v_reuseFailAlloc_3167_, 9, v_snapshotTasks_3015_);
v___x_3021_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v_mctx_3024_; lean_object* v_zetaDeltaFVarIds_3025_; lean_object* v_postponed_3026_; lean_object* v_diag_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3165_; 
v___x_3022_ = lean_st_ref_put(v___y_2873_, v___x_3021_);
v___x_3023_ = lean_st_ref_take(v___y_2871_);
v_mctx_3024_ = lean_ctor_get(v___x_3023_, 0);
v_zetaDeltaFVarIds_3025_ = lean_ctor_get(v___x_3023_, 2);
v_postponed_3026_ = lean_ctor_get(v___x_3023_, 3);
v_diag_3027_ = lean_ctor_get(v___x_3023_, 4);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; 
v_unused_3166_ = lean_ctor_get(v___x_3023_, 1);
lean_dec(v_unused_3166_);
v___x_3029_ = v___x_3023_;
v_isShared_3030_ = v_isSharedCheck_3165_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_diag_3027_);
lean_inc(v_postponed_3026_);
lean_inc(v_zetaDeltaFVarIds_3025_);
lean_inc(v_mctx_3024_);
lean_dec(v___x_3023_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3165_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 1, v___x_2952_);
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_mctx_3024_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_3164_, 2, v_zetaDeltaFVarIds_3025_);
lean_ctor_set(v_reuseFailAlloc_3164_, 3, v_postponed_3026_);
lean_ctor_set(v_reuseFailAlloc_3164_, 4, v_diag_3027_);
v___x_3032_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3033_ = lean_st_ref_put(v___y_2871_, v___x_3032_);
v___x_3034_ = l_Lean_Expr_const___override(v_name_2973_, v___x_2865_);
v___x_3035_ = l_Lean_mkAppN(v___x_3034_, v___x_2897_);
v___x_3036_ = lean_array_get(v___x_2860_, v_fs_2869_, v_val_2861_);
lean_dec_ref(v_fs_2869_);
v___x_3037_ = l_Lean_mkAppN(v___x_3036_, v___x_2899_);
lean_dec_ref(v___x_2899_);
v___x_3038_ = l_Lean_Meta_mkPProdSndM(v___x_2957_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_Expr_app___override(v___x_3037_, v_a_3039_);
v___x_3041_ = l_Lean_Meta_mkEq(v___x_3035_, v___x_3040_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc_n(v_a_3042_, 2);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = lean_box(0);
v___x_3044_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3042_, v___x_3043_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = l_Lean_Expr_mvarId_x21(v_a_3045_);
v___x_3047_ = l_Lean_Expr_fvarId_x21(v___x_2858_);
lean_dec_ref(v___x_2858_);
v___x_3048_ = lean_mk_empty_array_with_capacity(v___x_2867_);
v___x_3049_ = lean_box(0);
v___x_3050_ = l_Lean_MVarId_cases(v___x_3046_, v___x_3047_, v___x_3048_, v___x_2905_, v___x_3049_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; size_t v_sz_3053_; lean_object* v___x_3054_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = lean_box(0);
v_sz_3053_ = lean_array_size(v_a_3051_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3051_, v_sz_3053_, v___x_2880_, v___x_3052_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v_a_3051_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v___x_3055_; lean_object* v_a_3056_; lean_object* v___x_3057_; 
lean_dec_ref_known(v___x_3054_, 1);
v___x_3055_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3045_, v___y_2871_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = l_Lean_Meta_mkForallFVars(v___x_2897_, v_a_3042_, v___x_2905_, v___x_2862_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3059_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3059_ = l_Lean_Meta_mkLambdaFVars(v___x_2897_, v_a_3056_, v___x_2905_, v___x_2862_, v___x_2905_, v___x_2862_, v___x_2906_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec_ref(v___x_2897_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
lean_inc(v_brecOnEqName_2868_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 2, v_a_3058_);
lean_ctor_set(v___x_2975_, 1, v_levelParams_2864_);
lean_ctor_set(v___x_2975_, 0, v_brecOnEqName_2868_);
v___x_3062_ = v___x_2975_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_brecOnEqName_2868_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_levelParams_2864_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_a_3058_);
v___x_3062_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(0);
lean_inc(v_brecOnEqName_2868_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 1);
lean_ctor_set(v___x_2885_, 1, v___x_3063_);
lean_ctor_set(v___x_2885_, 0, v_brecOnEqName_2868_);
v___x_3065_ = v___x_2885_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_brecOnEqName_2868_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3067_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 2, v___x_3065_);
lean_ctor_set(v___x_2923_, 1, v_a_3060_);
lean_ctor_set(v___x_2923_, 0, v___x_3062_);
v___x_3067_ = v___x_2923_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v_a_3060_);
lean_ctor_set(v_reuseFailAlloc_3113_, 2, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; lean_object* v_a_3069_; lean_object* v___x_3070_; 
v___x_3068_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3067_, v___y_2873_);
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref(v___x_3068_);
v___x_3070_ = l_Lean_addDecl(v_a_3069_, v___x_2905_, v___y_2872_, v___y_2873_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3111_; 
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3112_);
v___x_3072_ = v___x_3070_;
v_isShared_3073_ = v_isSharedCheck_3111_;
goto v_resetjp_3071_;
}
else
{
lean_dec(v___x_3070_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3111_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v_env_3075_; lean_object* v_nextMacroScope_3076_; lean_object* v_ngen_3077_; lean_object* v_auxDeclNGen_3078_; lean_object* v_traceState_3079_; lean_object* v_recordedDeps_3080_; lean_object* v_messages_3081_; lean_object* v_infoState_3082_; lean_object* v_snapshotTasks_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3109_; 
v___x_3074_ = lean_st_ref_take(v___y_2873_);
v_env_3075_ = lean_ctor_get(v___x_3074_, 0);
v_nextMacroScope_3076_ = lean_ctor_get(v___x_3074_, 1);
v_ngen_3077_ = lean_ctor_get(v___x_3074_, 2);
v_auxDeclNGen_3078_ = lean_ctor_get(v___x_3074_, 3);
v_traceState_3079_ = lean_ctor_get(v___x_3074_, 4);
v_recordedDeps_3080_ = lean_ctor_get(v___x_3074_, 6);
v_messages_3081_ = lean_ctor_get(v___x_3074_, 7);
v_infoState_3082_ = lean_ctor_get(v___x_3074_, 8);
v_snapshotTasks_3083_ = lean_ctor_get(v___x_3074_, 9);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v___x_3074_, 5);
lean_dec(v_unused_3110_);
v___x_3085_ = v___x_3074_;
v_isShared_3086_ = v_isSharedCheck_3109_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_snapshotTasks_3083_);
lean_inc(v_infoState_3082_);
lean_inc(v_messages_3081_);
lean_inc(v_recordedDeps_3080_);
lean_inc(v_traceState_3079_);
lean_inc(v_auxDeclNGen_3078_);
lean_inc(v_ngen_3077_);
lean_inc(v_nextMacroScope_3076_);
lean_inc(v_env_3075_);
lean_dec(v___x_3074_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3109_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = l_Lean_addProtected(v_env_3075_, v_brecOnEqName_2868_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 5, v___x_2940_);
lean_ctor_set(v___x_3085_, 0, v___x_3087_);
v___x_3089_ = v___x_3085_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_nextMacroScope_3076_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_ngen_3077_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_auxDeclNGen_3078_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_traceState_3079_);
lean_ctor_set(v_reuseFailAlloc_3108_, 5, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_3108_, 6, v_recordedDeps_3080_);
lean_ctor_set(v_reuseFailAlloc_3108_, 7, v_messages_3081_);
lean_ctor_set(v_reuseFailAlloc_3108_, 8, v_infoState_3082_);
lean_ctor_set(v_reuseFailAlloc_3108_, 9, v_snapshotTasks_3083_);
v___x_3089_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v_mctx_3092_; lean_object* v_zetaDeltaFVarIds_3093_; lean_object* v_postponed_3094_; lean_object* v_diag_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3106_; 
v___x_3090_ = lean_st_ref_put(v___y_2873_, v___x_3089_);
v___x_3091_ = lean_st_ref_take(v___y_2871_);
v_mctx_3092_ = lean_ctor_get(v___x_3091_, 0);
v_zetaDeltaFVarIds_3093_ = lean_ctor_get(v___x_3091_, 2);
v_postponed_3094_ = lean_ctor_get(v___x_3091_, 3);
v_diag_3095_ = lean_ctor_get(v___x_3091_, 4);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; 
v_unused_3107_ = lean_ctor_get(v___x_3091_, 1);
lean_dec(v_unused_3107_);
v___x_3097_ = v___x_3091_;
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_diag_3095_);
lean_inc(v_postponed_3094_);
lean_inc(v_zetaDeltaFVarIds_3093_);
lean_inc(v_mctx_3092_);
lean_dec(v___x_3091_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_2952_);
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_mctx_3092_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_2952_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_zetaDeltaFVarIds_3093_);
lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_postponed_3094_);
lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_diag_3095_);
v___x_3100_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3101_ = lean_st_ref_put(v___y_2871_, v___x_3100_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3052_);
v___x_3103_ = v___x_3072_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3052_);
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
}
}
}
else
{
lean_dec(v_brecOnEqName_2868_);
return v___x_3070_;
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_a_3058_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
v_a_3116_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3059_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3059_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3056_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
v_a_3124_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3057_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3057_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
return v___x_3054_;
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3042_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
v_a_3132_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3050_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3050_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_a_3042_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3140_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3044_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3044_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3148_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3041_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3041_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref(v___x_3037_);
lean_dec_ref(v___x_3035_);
lean_del_object(v___x_2975_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3156_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3038_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3038_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
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
lean_dec(v_a_2965_);
lean_dec_ref(v___x_2957_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_a_2961_);
lean_dec_ref(v___x_2957_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3181_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_2962_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_2962_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref(v___x_2957_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3189_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_2960_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_2960_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v___x_2957_);
lean_del_object(v___x_2923_);
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec_ref(v___x_2858_);
v_a_3197_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_2958_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_2958_);
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
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
}
else
{
lean_dec(v_a_2913_);
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_a_2908_);
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
v_a_3216_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_2909_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_2909_);
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
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
v_a_3224_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_2907_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_2907_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___x_2900_);
lean_dec_ref(v___x_2899_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v___x_2891_);
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
v_a_3232_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_2903_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_2903_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_del_object(v___x_2885_);
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v___x_2857_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2850_);
v_a_3240_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_2888_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_2888_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_fs_2869_);
lean_dec(v_brecOnEqName_2868_);
lean_dec(v_brecOnName_2866_);
lean_dec(v___x_2865_);
lean_dec(v_levelParams_2864_);
lean_dec(v_brecOnGoName_2863_);
lean_dec_ref(v___x_2858_);
lean_dec_ref(v___x_2857_);
lean_dec_ref(v___x_2856_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2850_);
lean_dec(v___x_2847_);
v_a_3250_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_2881_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_2881_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3258_ = _args[0];
lean_object* v_tail_3259_ = _args[1];
lean_object* v_recName_3260_ = _args[2];
lean_object* v___x_3261_ = _args[3];
lean_object* v___x_3262_ = _args[4];
lean_object* v___x_3263_ = _args[5];
lean_object* v___x_3264_ = _args[6];
lean_object* v___x_3265_ = _args[7];
lean_object* v___x_3266_ = _args[8];
lean_object* v___x_3267_ = _args[9];
lean_object* v___x_3268_ = _args[10];
lean_object* v___x_3269_ = _args[11];
lean_object* v___x_3270_ = _args[12];
lean_object* v___x_3271_ = _args[13];
lean_object* v_val_3272_ = _args[14];
lean_object* v___x_3273_ = _args[15];
lean_object* v_brecOnGoName_3274_ = _args[16];
lean_object* v_levelParams_3275_ = _args[17];
lean_object* v___x_3276_ = _args[18];
lean_object* v_brecOnName_3277_ = _args[19];
lean_object* v___x_3278_ = _args[20];
lean_object* v_brecOnEqName_3279_ = _args[21];
lean_object* v_fs_3280_ = _args[22];
lean_object* v___y_3281_ = _args[23];
lean_object* v___y_3282_ = _args[24];
lean_object* v___y_3283_ = _args[25];
lean_object* v___y_3284_ = _args[26];
lean_object* v___y_3285_ = _args[27];
_start:
{
uint8_t v___x_30857__boxed_3286_; lean_object* v_res_3287_; 
v___x_30857__boxed_3286_ = lean_unbox(v___x_3273_);
v_res_3287_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3258_, v_tail_3259_, v_recName_3260_, v___x_3261_, v___x_3262_, v___x_3263_, v___x_3264_, v___x_3265_, v___x_3266_, v___x_3267_, v___x_3268_, v___x_3269_, v___x_3270_, v___x_3271_, v_val_3272_, v___x_30857__boxed_3286_, v_brecOnGoName_3274_, v_levelParams_3275_, v___x_3276_, v_brecOnName_3277_, v___x_3278_, v_brecOnEqName_3279_, v_fs_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___x_3278_);
lean_dec(v_val_3272_);
lean_dec_ref(v___x_3271_);
lean_dec(v___x_3270_);
lean_dec_ref(v___x_3266_);
lean_dec(v___x_3265_);
lean_dec(v___x_3264_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3288_, lean_object* v_a_3289_, uint8_t v___x_3290_, lean_object* v_f_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; 
lean_inc_ref(v_targs_3288_);
v___x_3297_ = lean_array_push(v_targs_3288_, v_f_3291_);
v___x_3298_ = l_Lean_mkAppN(v_a_3289_, v_targs_3288_);
lean_dec_ref(v_targs_3288_);
v___x_3299_ = 0;
v___x_3300_ = 1;
v___x_3301_ = l_Lean_Meta_mkForallFVars(v___x_3297_, v___x_3298_, v___x_3299_, v___x_3290_, v___x_3290_, v___x_3300_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec_ref(v___x_3297_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3302_, lean_object* v_a_3303_, lean_object* v___x_3304_, lean_object* v_f_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
uint8_t v___x_31571__boxed_3311_; lean_object* v_res_3312_; 
v___x_31571__boxed_3311_ = lean_unbox(v___x_3304_);
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3302_, v_a_3303_, v___x_31571__boxed_3311_, v_f_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3316_, uint8_t v___x_3317_, lean_object* v___x_3318_, lean_object* v_targs_3319_, lean_object* v_x_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3326_ = lean_box(v___x_3317_);
lean_inc_ref(v_targs_3319_);
v___f_3327_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3327_, 0, v_targs_3319_);
lean_closure_set(v___f_3327_, 1, v_a_3316_);
lean_closure_set(v___f_3327_, 2, v___x_3326_);
v___x_3328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3329_ = l_Lean_mkAppN(v___x_3318_, v_targs_3319_);
lean_dec_ref(v_targs_3319_);
v___x_3330_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3328_, v___x_3329_, v___f_3327_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3331_, lean_object* v___x_3332_, lean_object* v___x_3333_, lean_object* v_targs_3334_, lean_object* v_x_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v___x_31605__boxed_3341_; lean_object* v_res_3342_; 
v___x_31605__boxed_3341_ = lean_unbox(v___x_3332_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3331_, v___x_31605__boxed_3341_, v___x_3333_, v_targs_3334_, v_x_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v_x_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_a_3343_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3351_, lean_object* v_x_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3351_, v_x_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec_ref(v_x_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3360_, lean_object* v___x_3361_, lean_object* v_as_3362_, size_t v_sz_3363_, size_t v_i_3364_, lean_object* v_b_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_usize_dec_lt(v_i_3364_, v_sz_3363_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_b_3365_);
return v___x_3372_;
}
else
{
lean_object* v_snd_3373_; lean_object* v_fst_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3471_; 
v_snd_3373_ = lean_ctor_get(v_b_3365_, 1);
v_fst_3374_ = lean_ctor_get(v_b_3365_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v_b_3365_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3376_ = v_b_3365_;
v_isShared_3377_ = v_isSharedCheck_3471_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_snd_3373_);
lean_inc(v_fst_3374_);
lean_dec(v_b_3365_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3471_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_fst_3378_; lean_object* v_snd_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3470_; 
v_fst_3378_ = lean_ctor_get(v_snd_3373_, 0);
v_snd_3379_ = lean_ctor_get(v_snd_3373_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_snd_3373_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3381_ = v_snd_3373_;
v_isShared_3382_ = v_isSharedCheck_3470_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_snd_3379_);
lean_inc(v_fst_3378_);
lean_dec(v_snd_3373_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3470_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v_next_3391_; 
v_next_3391_ = lean_ctor_get(v_snd_3379_, 0);
lean_inc(v_next_3391_);
if (lean_obj_tag(v_next_3391_) == 0)
{
goto v___jp_3383_;
}
else
{
lean_object* v_upperBound_3392_; lean_object* v_val_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3469_; 
v_upperBound_3392_ = lean_ctor_get(v_snd_3379_, 1);
v_val_3393_ = lean_ctor_get(v_next_3391_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_next_3391_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3395_ = v_next_3391_;
v_isShared_3396_ = v_isSharedCheck_3469_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_val_3393_);
lean_dec(v_next_3391_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3469_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v___x_3397_; 
v___x_3397_ = lean_nat_dec_lt(v_val_3393_, v_upperBound_3392_);
if (v___x_3397_ == 0)
{
lean_del_object(v___x_3395_);
lean_dec(v_val_3393_);
goto v___jp_3383_;
}
else
{
lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3466_; 
lean_inc(v_upperBound_3392_);
lean_del_object(v___x_3381_);
lean_del_object(v___x_3376_);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_snd_3379_);
if (v_isSharedCheck_3466_ == 0)
{
lean_object* v_unused_3467_; lean_object* v_unused_3468_; 
v_unused_3467_ = lean_ctor_get(v_snd_3379_, 1);
lean_dec(v_unused_3467_);
v_unused_3468_ = lean_ctor_get(v_snd_3379_, 0);
lean_dec(v_unused_3468_);
v___x_3399_ = v_snd_3379_;
v_isShared_3400_ = v_isSharedCheck_3466_;
goto v_resetjp_3398_;
}
else
{
lean_dec(v_snd_3379_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3466_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v_array_3401_; lean_object* v_start_3402_; lean_object* v_stop_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
v_array_3401_ = lean_ctor_get(v_fst_3378_, 0);
v_start_3402_ = lean_ctor_get(v_fst_3378_, 1);
v_stop_3403_ = lean_ctor_get(v_fst_3378_, 2);
v___x_3404_ = lean_unsigned_to_nat(1u);
v___x_3405_ = lean_nat_add(v_val_3393_, v___x_3404_);
lean_dec(v_val_3393_);
lean_inc(v___x_3405_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3405_);
v___x_3407_ = v___x_3395_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3405_);
v___x_3407_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
lean_object* v___x_3409_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v___x_3407_);
v___x_3409_ = v___x_3399_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_upperBound_3392_);
v___x_3409_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
uint8_t v___x_3410_; 
v___x_3410_ = lean_nat_dec_lt(v_start_3402_, v_stop_3403_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec(v___x_3405_);
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_fst_3378_);
lean_ctor_set(v___x_3411_, 1, v___x_3409_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_fst_3374_);
lean_ctor_set(v___x_3412_, 1, v___x_3411_);
v___x_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
return v___x_3413_;
}
else
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3460_; 
lean_inc(v_stop_3403_);
lean_inc(v_start_3402_);
lean_inc_ref(v_array_3401_);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_fst_3378_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; lean_object* v_unused_3462_; lean_object* v_unused_3463_; 
v_unused_3461_ = lean_ctor_get(v_fst_3378_, 2);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_fst_3378_, 1);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_fst_3378_, 0);
lean_dec(v_unused_3463_);
v___x_3415_ = v_fst_3378_;
v_isShared_3416_ = v_isSharedCheck_3460_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_fst_3378_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3460_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
uint8_t v___x_3417_; lean_object* v_a_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3417_ = lean_nat_dec_lt(v___x_3360_, v___x_3361_);
v_a_3418_ = lean_array_uget_borrowed(v_as_3362_, v_i_3364_);
v___x_3419_ = lean_array_fget_borrowed(v_array_3401_, v_start_3402_);
v___x_3420_ = lean_box(v___x_3417_);
lean_inc(v___x_3419_);
lean_inc(v_a_3418_);
v___f_3421_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3421_, 0, v_a_3418_);
lean_closure_set(v___f_3421_, 1, v___x_3420_);
lean_closure_set(v___f_3421_, 2, v___x_3419_);
v___x_3422_ = lean_nat_add(v_start_3402_, v___x_3404_);
lean_dec(v_start_3402_);
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v___x_3422_);
v___x_3424_ = v___x_3415_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_array_3401_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v___x_3422_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_stop_3403_);
v___x_3424_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
lean_object* v___x_3425_; 
lean_inc(v___y_3369_);
lean_inc_ref(v___y_3368_);
lean_inc(v___y_3367_);
lean_inc_ref(v___y_3366_);
lean_inc(v_a_3418_);
v___x_3425_ = lean_infer_type(v_a_3418_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = 0;
v___x_3428_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3426_, v___f_3421_, v___x_3427_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___f_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; size_t v___x_3440_; size_t v___x_3441_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref_known(v___x_3428_, 1);
v___f_3430_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3430_, 0, v_a_3429_);
v___x_3431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3432_ = l_Nat_reprFast(v___x_3405_);
v___x_3433_ = lean_string_append(v___x_3431_, v___x_3432_);
lean_dec_ref(v___x_3432_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_Lean_Name_str___override(v___x_3434_, v___x_3433_);
v___x_3436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___f_3430_);
v___x_3437_ = lean_array_push(v_fst_3374_, v___x_3436_);
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3424_);
lean_ctor_set(v___x_3438_, 1, v___x_3409_);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = ((size_t)1ULL);
v___x_3441_ = lean_usize_add(v_i_3364_, v___x_3440_);
v_i_3364_ = v___x_3441_;
v_b_3365_ = v___x_3439_;
goto _start;
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v___x_3424_);
lean_dec_ref(v___x_3409_);
lean_dec(v___x_3405_);
lean_dec(v_fst_3374_);
v_a_3443_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3428_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3428_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v___x_3424_);
lean_dec_ref(v___f_3421_);
lean_dec_ref(v___x_3409_);
lean_dec(v___x_3405_);
lean_dec(v_fst_3374_);
v_a_3451_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3425_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3425_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
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
v___jp_3383_:
{
lean_object* v___x_3385_; 
if (v_isShared_3382_ == 0)
{
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_fst_3378_);
lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_snd_3379_);
v___x_3385_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v___x_3385_);
v___x_3387_ = v___x_3376_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_fst_3374_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3472_, lean_object* v___x_3473_, lean_object* v_as_3474_, lean_object* v_sz_3475_, lean_object* v_i_3476_, lean_object* v_b_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
size_t v_sz_boxed_3483_; size_t v_i_boxed_3484_; lean_object* v_res_3485_; 
v_sz_boxed_3483_ = lean_unbox_usize(v_sz_3475_);
lean_dec(v_sz_3475_);
v_i_boxed_3484_ = lean_unbox_usize(v_i_3476_);
lean_dec(v_i_3476_);
v_res_3485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3472_, v___x_3473_, v_as_3474_, v_sz_boxed_3483_, v_i_boxed_3484_, v_b_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec_ref(v_as_3474_);
lean_dec(v___x_3473_);
lean_dec(v___x_3472_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3486_, size_t v_i_3487_, lean_object* v_bs_3488_){
_start:
{
uint8_t v___x_3489_; 
v___x_3489_ = lean_usize_dec_lt(v_i_3487_, v_sz_3486_);
if (v___x_3489_ == 0)
{
return v_bs_3488_;
}
else
{
lean_object* v_v_3490_; lean_object* v_fst_3491_; lean_object* v_snd_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3508_; 
v_v_3490_ = lean_array_uget(v_bs_3488_, v_i_3487_);
v_fst_3491_ = lean_ctor_get(v_v_3490_, 0);
v_snd_3492_ = lean_ctor_get(v_v_3490_, 1);
v_isSharedCheck_3508_ = !lean_is_exclusive(v_v_3490_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3494_ = v_v_3490_;
v_isShared_3495_ = v_isSharedCheck_3508_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_snd_3492_);
lean_inc(v_fst_3491_);
lean_dec(v_v_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3508_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v_bs_x27_3497_; uint8_t v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3496_ = lean_unsigned_to_nat(0u);
v_bs_x27_3497_ = lean_array_uset(v_bs_3488_, v_i_3487_, v___x_3496_);
v___x_3498_ = 0;
v___x_3499_ = lean_box(v___x_3498_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3499_);
v___x_3501_ = v___x_3494_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_snd_3492_);
v___x_3501_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; size_t v___x_3503_; size_t v___x_3504_; lean_object* v___x_3505_; 
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_fst_3491_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = ((size_t)1ULL);
v___x_3504_ = lean_usize_add(v_i_3487_, v___x_3503_);
v___x_3505_ = lean_array_uset(v_bs_x27_3497_, v_i_3487_, v___x_3502_);
v_i_3487_ = v___x_3504_;
v_bs_3488_ = v___x_3505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3509_, lean_object* v_i_3510_, lean_object* v_bs_3511_){
_start:
{
size_t v_sz_boxed_3512_; size_t v_i_boxed_3513_; lean_object* v_res_3514_; 
v_sz_boxed_3512_ = lean_unbox_usize(v_sz_3509_);
lean_dec(v_sz_3509_);
v_i_boxed_3513_ = lean_unbox_usize(v_i_3510_);
lean_dec(v_i_3510_);
v_res_3514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3512_, v_i_boxed_3513_, v_bs_3511_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3515_, lean_object* v___x_3516_, lean_object* v_a_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_30400__overap_3523_; lean_object* v___x_3524_; 
v___x_30400__overap_3523_ = l_instInhabitedOfMonad___redArg(v___x_3515_, v___x_3516_);
lean_inc(v___y_3521_);
lean_inc_ref(v___y_3520_);
lean_inc(v___y_3519_);
lean_inc_ref(v___y_3518_);
v___x_3524_ = lean_apply_5(v___x_30400__overap_3523_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, lean_box(0));
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3525_, lean_object* v___x_3526_, lean_object* v_a_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3525_, v___x_3526_, v_a_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v_a_3527_);
return v_res_3533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_instMonadEIO___redArg();
return v___x_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3536_ = l_StateRefT_x27_instMonad___redArg(v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3541_, lean_object* v_declInfos_3542_, lean_object* v_k_3543_, lean_object* v_kind_3544_, lean_object* v_b_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
uint8_t v_kind_boxed_3551_; lean_object* v_res_3552_; 
v_kind_boxed_3551_ = lean_unbox(v_kind_3544_);
v_res_3552_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3541_, v_declInfos_3542_, v_k_3543_, v_kind_boxed_3551_, v_b_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3553_, lean_object* v_declInfos_3554_, lean_object* v_k_3555_, uint8_t v_kind_3556_, lean_object* v_name_3557_, uint8_t v_bi_3558_, lean_object* v_type_3559_, uint8_t v_kind_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v___f_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_box(v_kind_3556_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3567_, 0, v_acc_3553_);
lean_closure_set(v___f_3567_, 1, v_declInfos_3554_);
lean_closure_set(v___f_3567_, 2, v_k_3555_);
lean_closure_set(v___f_3567_, 3, v___x_3566_);
v___x_3568_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3557_, v_bi_3558_, v_type_3559_, v___f_3567_, v_kind_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3568_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3568_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3585_, lean_object* v_k_3586_, uint8_t v_kind_3587_, lean_object* v_acc_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; lean_object* v_toApplicative_3595_; lean_object* v_toFunctor_3596_; lean_object* v_toSeq_3597_; lean_object* v_toSeqLeft_3598_; lean_object* v_toSeqRight_3599_; lean_object* v___f_3600_; lean_object* v___f_3601_; lean_object* v___f_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___f_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v_toApplicative_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3667_; 
v___x_3594_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3595_ = lean_ctor_get(v___x_3594_, 0);
v_toFunctor_3596_ = lean_ctor_get(v_toApplicative_3595_, 0);
v_toSeq_3597_ = lean_ctor_get(v_toApplicative_3595_, 2);
v_toSeqLeft_3598_ = lean_ctor_get(v_toApplicative_3595_, 3);
v_toSeqRight_3599_ = lean_ctor_get(v_toApplicative_3595_, 4);
v___f_3600_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3601_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3596_, 2);
v___f_3602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3602_, 0, v_toFunctor_3596_);
v___f_3603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3603_, 0, v_toFunctor_3596_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___f_3602_);
lean_ctor_set(v___x_3604_, 1, v___f_3603_);
lean_inc(v_toSeqRight_3599_);
v___f_3605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3605_, 0, v_toSeqRight_3599_);
lean_inc(v_toSeqLeft_3598_);
v___f_3606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3606_, 0, v_toSeqLeft_3598_);
lean_inc(v_toSeq_3597_);
v___f_3607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3607_, 0, v_toSeq_3597_);
v___x_3608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3604_);
lean_ctor_set(v___x_3608_, 1, v___f_3600_);
lean_ctor_set(v___x_3608_, 2, v___f_3607_);
lean_ctor_set(v___x_3608_, 3, v___f_3606_);
lean_ctor_set(v___x_3608_, 4, v___f_3605_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
lean_ctor_set(v___x_3609_, 1, v___f_3601_);
v___x_3610_ = l_StateRefT_x27_instMonad___redArg(v___x_3609_);
v_toApplicative_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; 
v_unused_3668_ = lean_ctor_get(v___x_3610_, 1);
lean_dec(v_unused_3668_);
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3667_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_toApplicative_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3667_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v_toFunctor_3615_; lean_object* v_toSeq_3616_; lean_object* v_toSeqLeft_3617_; lean_object* v_toSeqRight_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3665_; 
v_toFunctor_3615_ = lean_ctor_get(v_toApplicative_3611_, 0);
v_toSeq_3616_ = lean_ctor_get(v_toApplicative_3611_, 2);
v_toSeqLeft_3617_ = lean_ctor_get(v_toApplicative_3611_, 3);
v_toSeqRight_3618_ = lean_ctor_get(v_toApplicative_3611_, 4);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_toApplicative_3611_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_toApplicative_3611_, 1);
lean_dec(v_unused_3666_);
v___x_3620_ = v_toApplicative_3611_;
v_isShared_3621_ = v_isSharedCheck_3665_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_toSeqRight_3618_);
lean_inc(v_toSeqLeft_3617_);
lean_inc(v_toSeq_3616_);
lean_inc(v_toFunctor_3615_);
lean_dec(v_toApplicative_3611_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3665_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___f_3629_; lean_object* v___x_3631_; 
v___f_3622_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3623_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3615_);
v___f_3624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3624_, 0, v_toFunctor_3615_);
v___f_3625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3625_, 0, v_toFunctor_3615_);
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v___f_3624_);
lean_ctor_set(v___x_3626_, 1, v___f_3625_);
v___f_3627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3627_, 0, v_toSeqRight_3618_);
v___f_3628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3628_, 0, v_toSeqLeft_3617_);
v___f_3629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3629_, 0, v_toSeq_3616_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 4, v___f_3627_);
lean_ctor_set(v___x_3620_, 3, v___f_3628_);
lean_ctor_set(v___x_3620_, 2, v___f_3629_);
lean_ctor_set(v___x_3620_, 1, v___f_3622_);
lean_ctor_set(v___x_3620_, 0, v___x_3626_);
v___x_3631_ = v___x_3620_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___f_3622_);
lean_ctor_set(v_reuseFailAlloc_3664_, 2, v___f_3629_);
lean_ctor_set(v_reuseFailAlloc_3664_, 3, v___f_3628_);
lean_ctor_set(v_reuseFailAlloc_3664_, 4, v___f_3627_);
v___x_3631_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 1, v___f_3623_);
lean_ctor_set(v___x_3613_, 0, v___x_3631_);
v___x_3633_ = v___x_3613_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___f_3623_);
v___x_3633_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3634_ = lean_array_get_size(v_acc_3588_);
v___x_3635_ = lean_array_get_size(v_declInfos_3585_);
v___x_3636_ = lean_nat_dec_lt(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec_ref(v___x_3633_);
lean_dec_ref(v_declInfos_3585_);
lean_inc(v___y_3592_);
lean_inc_ref(v___y_3591_);
lean_inc(v___y_3590_);
lean_inc_ref(v___y_3589_);
v___x_3637_ = lean_apply_6(v_k_3586_, v_acc_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, lean_box(0));
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___f_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_snd_3647_; lean_object* v_fst_3648_; lean_object* v_fst_3649_; lean_object* v_snd_3650_; lean_object* v___x_3651_; 
v___x_3638_ = lean_box(0);
v___x_3639_ = 0;
v___x_3640_ = l_Lean_instInhabitedExpr;
v___f_3641_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3641_, 0, v___x_3633_);
lean_closure_set(v___f_3641_, 1, v___x_3640_);
v___f_3642_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3642_, 0, v___f_3641_);
v___x_3643_ = lean_box(v___x_3639_);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v___f_3642_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3638_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_array_get(v___x_3645_, v_declInfos_3585_, v___x_3634_);
lean_dec_ref_known(v___x_3645_, 2);
v_snd_3647_ = lean_ctor_get(v___x_3646_, 1);
lean_inc(v_snd_3647_);
v_fst_3648_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_fst_3648_);
lean_dec(v___x_3646_);
v_fst_3649_ = lean_ctor_get(v_snd_3647_, 0);
lean_inc(v_fst_3649_);
v_snd_3650_ = lean_ctor_get(v_snd_3647_, 1);
lean_inc(v_snd_3650_);
lean_dec(v_snd_3647_);
lean_inc(v___y_3592_);
lean_inc_ref(v___y_3591_);
lean_inc(v___y_3590_);
lean_inc_ref(v___y_3589_);
lean_inc_ref(v_acc_3588_);
v___x_3651_ = lean_apply_6(v_snd_3650_, v_acc_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, lean_box(0));
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v___x_3653_ = lean_unbox(v_fst_3649_);
lean_dec(v_fst_3649_);
v___x_3654_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3588_, v_declInfos_3585_, v_k_3586_, v_kind_3587_, v_fst_3648_, v___x_3653_, v_a_3652_, v_kind_3587_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3654_;
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
lean_dec(v_fst_3649_);
lean_dec(v_fst_3648_);
lean_dec_ref(v_acc_3588_);
lean_dec_ref(v_k_3586_);
lean_dec_ref(v_declInfos_3585_);
v_a_3655_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3651_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3651_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3660_; 
if (v_isShared_3658_ == 0)
{
v___x_3660_ = v___x_3657_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3669_, lean_object* v_declInfos_3670_, lean_object* v_k_3671_, uint8_t v_kind_3672_, lean_object* v_b_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = lean_array_push(v_acc_3669_, v_b_3673_);
v___x_3680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3670_, v_k_3671_, v_kind_3672_, v___x_3679_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3681_, lean_object* v_declInfos_3682_, lean_object* v_k_3683_, lean_object* v_kind_3684_, lean_object* v_name_3685_, lean_object* v_bi_3686_, lean_object* v_type_3687_, lean_object* v_kind_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
uint8_t v_kind_boxed_3694_; uint8_t v_bi_boxed_3695_; uint8_t v_kind_boxed_3696_; lean_object* v_res_3697_; 
v_kind_boxed_3694_ = lean_unbox(v_kind_3684_);
v_bi_boxed_3695_ = lean_unbox(v_bi_3686_);
v_kind_boxed_3696_ = lean_unbox(v_kind_3688_);
v_res_3697_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3681_, v_declInfos_3682_, v_k_3683_, v_kind_boxed_3694_, v_name_3685_, v_bi_boxed_3695_, v_type_3687_, v_kind_boxed_3696_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3698_, lean_object* v_k_3699_, lean_object* v_kind_3700_, lean_object* v_acc_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_kind_boxed_3707_; lean_object* v_res_3708_; 
v_kind_boxed_3707_ = lean_unbox(v_kind_3700_);
v_res_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3698_, v_k_3699_, v_kind_boxed_3707_, v_acc_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3709_, lean_object* v_k_3710_, uint8_t v_kind_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3709_, v_k_3710_, v_kind_3711_, v___x_3717_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3719_, lean_object* v_k_3720_, lean_object* v_kind_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v_kind_boxed_3727_; lean_object* v_res_3728_; 
v_kind_boxed_3727_ = lean_unbox(v_kind_3721_);
v_res_3728_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3719_, v_k_3720_, v_kind_boxed_3727_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3729_, lean_object* v_k_3730_, uint8_t v_kind_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
size_t v_sz_3737_; size_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v_sz_3737_ = lean_array_size(v_declInfos_3729_);
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3737_, v___x_3738_, v_declInfos_3729_);
v___x_3740_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3739_, v_k_3730_, v_kind_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3741_, lean_object* v_k_3742_, lean_object* v_kind_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
uint8_t v_kind_boxed_3749_; lean_object* v_res_3750_; 
v_kind_boxed_3749_ = lean_unbox(v_kind_3743_);
v_res_3750_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3741_, v_k_3742_, v_kind_boxed_3749_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
lean_dec(v___y_3747_);
lean_dec_ref(v___y_3746_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
return v_res_3750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3752_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3753_ = lean_unsigned_to_nat(4u);
v___x_3754_ = lean_unsigned_to_nat(202u);
v___x_3755_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3757_ = l_mkPanicMessageWithDecl(v___x_3756_, v___x_3755_, v___x_3754_, v___x_3753_, v___x_3752_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3764_ = l_Lean_stringToMessageData(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3767_ = l_Lean_stringToMessageData(v___x_3766_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3768_, lean_object* v_numMotives_3769_, lean_object* v_numMinors_3770_, lean_object* v___x_3771_, lean_object* v_all_3772_, lean_object* v___x_3773_, lean_object* v___x_3774_, lean_object* v_head_3775_, lean_object* v_tail_3776_, lean_object* v_recName_3777_, lean_object* v_brecOnGoName_3778_, lean_object* v_levelParams_3779_, lean_object* v_brecOnName_3780_, lean_object* v_brecOnEqName_3781_, lean_object* v_type_3782_, lean_object* v_refArgs_3783_, lean_object* v_refBody_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v___x_3790_ = lean_nat_add(v_nParams_3768_, v_numMotives_3769_);
v___x_3791_ = lean_nat_add(v___x_3790_, v_numMinors_3770_);
v___x_3792_ = lean_array_get_size(v_refArgs_3783_);
v___x_3793_ = lean_nat_dec_lt(v___x_3791_, v___x_3792_);
if (v___x_3793_ == 0)
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec_ref(v_refArgs_3783_);
lean_dec_ref(v_type_3782_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3773_);
lean_dec_ref(v_all_3772_);
lean_dec(v___x_3771_);
lean_dec(v_nParams_3768_);
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3795_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3794_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3795_;
}
else
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3796_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3768_);
lean_inc_ref_n(v_refArgs_3783_, 2);
v___x_3797_ = l_Array_toSubarray___redArg(v_refArgs_3783_, v___x_3796_, v_nParams_3768_);
lean_inc(v___x_3790_);
v___x_3798_ = l_Array_toSubarray___redArg(v_refArgs_3783_, v_nParams_3768_, v___x_3790_);
v___x_3799_ = l_Subarray_copy___redArg(v___x_3798_);
v___x_3800_ = l_Lean_Expr_getAppFn(v_refBody_3784_);
v___x_3801_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3799_, v___x_3800_);
lean_dec_ref(v___x_3800_);
if (lean_obj_tag(v___x_3801_) == 1)
{
lean_object* v_val_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___f_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec_ref(v_type_3782_);
v_val_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3802_);
lean_dec_ref_known(v___x_3801_, 1);
lean_inc_n(v___x_3791_, 2);
lean_inc_ref_n(v_refArgs_3783_, 2);
v___x_3803_ = l_Array_toSubarray___redArg(v_refArgs_3783_, v___x_3790_, v___x_3791_);
v___x_3804_ = l_Subarray_copy___redArg(v___x_3797_);
v___x_3805_ = l_Subarray_copy___redArg(v___x_3803_);
v___x_3806_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3799_);
lean_inc_ref(v___x_3804_);
lean_inc(v___x_3771_);
v___f_3807_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3807_, 0, v___x_3771_);
lean_closure_set(v___f_3807_, 1, v___x_3804_);
lean_closure_set(v___f_3807_, 2, v___x_3799_);
lean_closure_set(v___f_3807_, 3, v_all_3772_);
lean_closure_set(v___f_3807_, 4, v___x_3773_);
lean_closure_set(v___f_3807_, 5, v___x_3796_);
lean_closure_set(v___f_3807_, 6, v___x_3806_);
v___x_3808_ = lean_nat_sub(v___x_3792_, v___x_3806_);
lean_inc(v___x_3808_);
v___x_3809_ = l_Array_toSubarray___redArg(v_refArgs_3783_, v___x_3791_, v___x_3808_);
v___x_3810_ = l_Subarray_copy___redArg(v___x_3809_);
v___x_3811_ = lean_array_get(v___x_3774_, v_refArgs_3783_, v___x_3808_);
lean_dec(v___x_3808_);
lean_dec_ref(v_refArgs_3783_);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v___y_3786_);
lean_inc_ref(v___y_3785_);
lean_inc(v___x_3811_);
v___x_3812_ = lean_infer_type(v___x_3811_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
lean_inc(v___y_3788_);
lean_inc_ref(v___y_3787_);
lean_inc(v___y_3786_);
lean_inc_ref(v___y_3785_);
v___x_3814_ = lean_infer_type(v_a_3813_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v_a_3815_; lean_object* v___x_3816_; 
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___x_3816_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3815_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
if (lean_obj_tag(v_a_3817_) == 1)
{
lean_object* v_val_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___f_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; size_t v_sz_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v_val_3818_ = lean_ctor_get(v_a_3817_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v_a_3817_, 1);
v___x_3819_ = l_Lean_mkLevelMax(v_val_3818_, v_head_3775_);
v___x_3820_ = lean_array_get_size(v___x_3799_);
v___x_3821_ = l_Array_ofFn___redArg(v___x_3820_, v___f_3807_);
v___x_3822_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3823_ = lean_array_get_size(v___x_3821_);
lean_inc_ref(v___x_3821_);
v___x_3824_ = l_Array_toSubarray___redArg(v___x_3821_, v___x_3796_, v___x_3823_);
v___x_3825_ = lean_box(v___x_3793_);
lean_inc(v___x_3791_);
lean_inc_ref(v___x_3799_);
lean_inc_ref(v___x_3824_);
v___f_3826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3826_, 0, v___x_3819_);
lean_closure_set(v___f_3826_, 1, v_tail_3776_);
lean_closure_set(v___f_3826_, 2, v_recName_3777_);
lean_closure_set(v___f_3826_, 3, v___x_3804_);
lean_closure_set(v___f_3826_, 4, v___x_3824_);
lean_closure_set(v___f_3826_, 5, v___x_3799_);
lean_closure_set(v___f_3826_, 6, v___x_3791_);
lean_closure_set(v___f_3826_, 7, v___x_3792_);
lean_closure_set(v___f_3826_, 8, v___x_3805_);
lean_closure_set(v___f_3826_, 9, v___x_3821_);
lean_closure_set(v___f_3826_, 10, v___x_3810_);
lean_closure_set(v___f_3826_, 11, v___x_3811_);
lean_closure_set(v___f_3826_, 12, v___x_3806_);
lean_closure_set(v___f_3826_, 13, v___x_3774_);
lean_closure_set(v___f_3826_, 14, v_val_3802_);
lean_closure_set(v___f_3826_, 15, v___x_3825_);
lean_closure_set(v___f_3826_, 16, v_brecOnGoName_3778_);
lean_closure_set(v___f_3826_, 17, v_levelParams_3779_);
lean_closure_set(v___f_3826_, 18, v___x_3771_);
lean_closure_set(v___f_3826_, 19, v_brecOnName_3780_);
lean_closure_set(v___f_3826_, 20, v___x_3796_);
lean_closure_set(v___f_3826_, 21, v_brecOnEqName_3781_);
v___x_3827_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
lean_ctor_set(v___x_3828_, 1, v___x_3820_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3824_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3822_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v_sz_3831_ = lean_array_size(v___x_3799_);
v___x_3832_ = ((size_t)0ULL);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3791_, v___x_3792_, v___x_3799_, v_sz_3831_, v___x_3832_, v___x_3830_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3791_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v_fst_3835_; uint8_t v___x_3836_; lean_object* v___x_3837_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v_fst_3835_ = lean_ctor_get(v_a_3834_, 0);
lean_inc(v_fst_3835_);
lean_dec(v_a_3834_);
v___x_3836_ = 0;
v___x_3837_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3835_, v___f_3826_, v___x_3836_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3837_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v___f_3826_);
v_a_3838_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3833_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3833_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
else
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
lean_dec(v_a_3817_);
lean_dec_ref(v___x_3810_);
lean_dec_ref(v___f_3807_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3804_);
lean_dec(v_val_3802_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3791_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3771_);
v___x_3846_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3847_ = l_Lean_MessageData_ofExpr(v___x_3811_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___x_3849_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3848_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3850_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3851_;
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v___x_3811_);
lean_dec_ref(v___x_3810_);
lean_dec_ref(v___f_3807_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3804_);
lean_dec(v_val_3802_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3791_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3771_);
v_a_3852_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3816_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3816_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v___x_3811_);
lean_dec_ref(v___x_3810_);
lean_dec_ref(v___f_3807_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3804_);
lean_dec(v_val_3802_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3791_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3771_);
v_a_3860_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3814_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3814_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec(v___x_3811_);
lean_dec_ref(v___x_3810_);
lean_dec_ref(v___f_3807_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3804_);
lean_dec(v_val_3802_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3791_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3771_);
v_a_3868_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3812_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3812_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
lean_dec(v___x_3801_);
lean_dec_ref(v___x_3797_);
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec_ref(v_refArgs_3783_);
lean_dec(v_brecOnEqName_3781_);
lean_dec(v_brecOnName_3780_);
lean_dec(v_levelParams_3779_);
lean_dec(v_brecOnGoName_3778_);
lean_dec(v_recName_3777_);
lean_dec(v_tail_3776_);
lean_dec(v_head_3775_);
lean_dec_ref(v___x_3774_);
lean_dec(v___x_3773_);
lean_dec_ref(v_all_3772_);
lean_dec(v___x_3771_);
v___x_3876_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3877_ = l_Lean_MessageData_ofExpr(v_type_3782_);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = lean_array_to_list(v___x_3799_);
v___x_3882_ = lean_box(0);
v___x_3883_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3881_, v___x_3882_);
v___x_3884_ = l_Lean_MessageData_ofList(v___x_3883_);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3880_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3885_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3887_ = _args[0];
lean_object* v_numMotives_3888_ = _args[1];
lean_object* v_numMinors_3889_ = _args[2];
lean_object* v___x_3890_ = _args[3];
lean_object* v_all_3891_ = _args[4];
lean_object* v___x_3892_ = _args[5];
lean_object* v___x_3893_ = _args[6];
lean_object* v_head_3894_ = _args[7];
lean_object* v_tail_3895_ = _args[8];
lean_object* v_recName_3896_ = _args[9];
lean_object* v_brecOnGoName_3897_ = _args[10];
lean_object* v_levelParams_3898_ = _args[11];
lean_object* v_brecOnName_3899_ = _args[12];
lean_object* v_brecOnEqName_3900_ = _args[13];
lean_object* v_type_3901_ = _args[14];
lean_object* v_refArgs_3902_ = _args[15];
lean_object* v_refBody_3903_ = _args[16];
lean_object* v___y_3904_ = _args[17];
lean_object* v___y_3905_ = _args[18];
lean_object* v___y_3906_ = _args[19];
lean_object* v___y_3907_ = _args[20];
lean_object* v___y_3908_ = _args[21];
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3887_, v_numMotives_3888_, v_numMinors_3889_, v___x_3890_, v_all_3891_, v___x_3892_, v___x_3893_, v_head_3894_, v_tail_3895_, v_recName_3896_, v_brecOnGoName_3897_, v_levelParams_3898_, v_brecOnName_3899_, v_brecOnEqName_3900_, v_type_3901_, v_refArgs_3902_, v_refBody_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec_ref(v_refBody_3903_);
lean_dec(v_numMinors_3889_);
lean_dec(v_numMotives_3888_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3912_, lean_object* v_nParams_3913_, lean_object* v_all_3914_, lean_object* v_brecOnName_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v_brecOnGoName_3924_; lean_object* v___x_3925_; lean_object* v_brecOnEqName_3926_; lean_object* v___x_3927_; 
v___x_3921_ = l_Lean_instInhabitedExpr;
v___x_3922_ = lean_box(0);
v___x_3923_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3915_, 2);
v_brecOnGoName_3924_ = l_Lean_Name_str___override(v_brecOnName_3915_, v___x_3923_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3926_ = l_Lean_Name_str___override(v_brecOnName_3915_, v___x_3925_);
lean_inc(v_recName_3912_);
v___x_3927_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3912_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3955_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3955_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3955_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
if (lean_obj_tag(v_a_3928_) == 7)
{
lean_object* v_val_3932_; lean_object* v_toConstantVal_3933_; lean_object* v_numMotives_3934_; lean_object* v_numMinors_3935_; lean_object* v_levelParams_3936_; lean_object* v_type_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_del_object(v___x_3930_);
v_val_3932_ = lean_ctor_get(v_a_3928_, 0);
lean_inc_ref(v_val_3932_);
lean_dec_ref_known(v_a_3928_, 1);
v_toConstantVal_3933_ = lean_ctor_get(v_val_3932_, 0);
lean_inc_ref(v_toConstantVal_3933_);
v_numMotives_3934_ = lean_ctor_get(v_val_3932_, 4);
lean_inc(v_numMotives_3934_);
v_numMinors_3935_ = lean_ctor_get(v_val_3932_, 5);
lean_inc(v_numMinors_3935_);
lean_dec_ref(v_val_3932_);
v_levelParams_3936_ = lean_ctor_get(v_toConstantVal_3933_, 1);
lean_inc_n(v_levelParams_3936_, 2);
v_type_3937_ = lean_ctor_get(v_toConstantVal_3933_, 2);
lean_inc_ref(v_type_3937_);
lean_dec_ref(v_toConstantVal_3933_);
v___x_3938_ = lean_box(0);
v___x_3939_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3936_, v___x_3938_);
if (lean_obj_tag(v___x_3939_) == 1)
{
lean_object* v_head_3940_; lean_object* v_tail_3941_; lean_object* v___f_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; 
v_head_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_head_3940_);
v_tail_3941_ = lean_ctor_get(v___x_3939_, 1);
lean_inc(v_tail_3941_);
lean_inc_ref(v_type_3937_);
v___f_3942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3942_, 0, v_nParams_3913_);
lean_closure_set(v___f_3942_, 1, v_numMotives_3934_);
lean_closure_set(v___f_3942_, 2, v_numMinors_3935_);
lean_closure_set(v___f_3942_, 3, v___x_3939_);
lean_closure_set(v___f_3942_, 4, v_all_3914_);
lean_closure_set(v___f_3942_, 5, v___x_3922_);
lean_closure_set(v___f_3942_, 6, v___x_3921_);
lean_closure_set(v___f_3942_, 7, v_head_3940_);
lean_closure_set(v___f_3942_, 8, v_tail_3941_);
lean_closure_set(v___f_3942_, 9, v_recName_3912_);
lean_closure_set(v___f_3942_, 10, v_brecOnGoName_3924_);
lean_closure_set(v___f_3942_, 11, v_levelParams_3936_);
lean_closure_set(v___f_3942_, 12, v_brecOnName_3915_);
lean_closure_set(v___f_3942_, 13, v_brecOnEqName_3926_);
lean_closure_set(v___f_3942_, 14, v_type_3937_);
v___x_3943_ = 0;
v___x_3944_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3937_, v___f_3942_, v___x_3943_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_dec(v___x_3939_);
lean_dec_ref(v_type_3937_);
lean_dec(v_levelParams_3936_);
lean_dec(v_numMinors_3935_);
lean_dec(v_numMotives_3934_);
lean_dec(v_brecOnEqName_3926_);
lean_dec(v_brecOnGoName_3924_);
lean_dec(v_brecOnName_3915_);
lean_dec_ref(v_all_3914_);
lean_dec(v_nParams_3913_);
v___x_3945_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3946_ = l_Lean_MessageData_ofName(v_recName_3912_);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3949_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3950_;
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
lean_dec(v_a_3928_);
lean_dec(v_brecOnEqName_3926_);
lean_dec(v_brecOnGoName_3924_);
lean_dec(v_brecOnName_3915_);
lean_dec_ref(v_all_3914_);
lean_dec(v_nParams_3913_);
lean_dec(v_recName_3912_);
v___x_3951_ = lean_box(0);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3951_);
v___x_3953_ = v___x_3930_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec(v_brecOnEqName_3926_);
lean_dec(v_brecOnGoName_3924_);
lean_dec(v_brecOnName_3915_);
lean_dec_ref(v_all_3914_);
lean_dec(v_nParams_3913_);
lean_dec(v_recName_3912_);
v_a_3956_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3927_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3927_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3964_, lean_object* v_nParams_3965_, lean_object* v_all_3966_, lean_object* v_brecOnName_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3964_, v_nParams_3965_, v_all_3966_, v_brecOnName_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3974_, lean_object* v___x_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v_a_3979_, lean_object* v_b_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v___x_3986_; 
v___x_3986_ = lean_nat_dec_lt(v_a_3979_, v_upperBound_3974_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; 
lean_dec(v_a_3979_);
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3977_);
lean_dec(v___x_3976_);
lean_dec(v___x_3975_);
v___x_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_b_3980_);
return v___x_3987_;
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = lean_unsigned_to_nat(1u);
v___x_3990_ = lean_nat_add(v_a_3979_, v___x_3989_);
lean_dec(v_a_3979_);
lean_inc_n(v___x_3990_, 2);
lean_inc(v___x_3975_);
v___x_3991_ = lean_name_append_index_after(v___x_3975_, v___x_3990_);
lean_inc(v___x_3976_);
v___x_3992_ = lean_name_append_index_after(v___x_3976_, v___x_3990_);
lean_inc_ref(v___x_3978_);
lean_inc(v___x_3977_);
v___x_3993_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3991_, v___x_3977_, v___x_3978_, v___x_3992_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_dec_ref_known(v___x_3993_, 1);
v_a_3979_ = v___x_3990_;
v_b_3980_ = v___x_3988_;
goto _start;
}
else
{
lean_dec(v___x_3990_);
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3977_);
lean_dec(v___x_3976_);
lean_dec(v___x_3975_);
return v___x_3993_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3995_, lean_object* v___x_3996_, lean_object* v___x_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v_a_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3995_, v___x_3996_, v___x_3997_, v___x_3998_, v___x_3999_, v_a_4000_, v_b_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v_upperBound_3995_);
return v_res_4007_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4012_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4013_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_4014_ = l_Lean_Name_append(v___x_4013_, v___x_4012_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_toCold_4021_; lean_object* v_options_4022_; lean_object* v_inheritedTraceOptions_4023_; uint8_t v_hasTrace_4024_; lean_object* v___x_4025_; 
v_toCold_4021_ = lean_ctor_get(v_a_4018_, 0);
v_options_4022_ = lean_ctor_get(v_toCold_4021_, 2);
v_inheritedTraceOptions_4023_ = lean_ctor_get(v_toCold_4021_, 11);
v_hasTrace_4024_ = lean_ctor_get_uint8(v_options_4022_, sizeof(void*)*1);
v___x_4025_ = lean_box(0);
if (v_hasTrace_4024_ == 0)
{
lean_object* v___x_4026_; 
lean_inc(v_indName_4015_);
v___x_4026_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4091_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4029_ = v___x_4026_;
v_isShared_4030_ = v_isSharedCheck_4091_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_4026_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4091_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
if (lean_obj_tag(v_a_4027_) == 5)
{
lean_object* v_val_4031_; uint8_t v_isRec_4032_; 
v_val_4031_ = lean_ctor_get(v_a_4027_, 0);
lean_inc_ref(v_val_4031_);
lean_dec_ref_known(v_a_4027_, 1);
v_isRec_4032_ = lean_ctor_get_uint8(v_val_4031_, sizeof(void*)*6);
if (v_isRec_4032_ == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4035_; 
lean_dec_ref(v_val_4031_);
lean_dec(v_indName_4015_);
v___x_4033_ = lean_box(0);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4033_);
v___x_4035_ = v___x_4029_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
else
{
lean_object* v_toConstantVal_4037_; lean_object* v_numParams_4038_; lean_object* v_all_4039_; lean_object* v_numNested_4040_; lean_object* v_type_4041_; lean_object* v___x_4042_; 
lean_del_object(v___x_4029_);
v_toConstantVal_4037_ = lean_ctor_get(v_val_4031_, 0);
lean_inc_ref(v_toConstantVal_4037_);
v_numParams_4038_ = lean_ctor_get(v_val_4031_, 1);
lean_inc(v_numParams_4038_);
v_all_4039_ = lean_ctor_get(v_val_4031_, 3);
lean_inc(v_all_4039_);
v_numNested_4040_ = lean_ctor_get(v_val_4031_, 5);
lean_inc(v_numNested_4040_);
lean_dec_ref(v_val_4031_);
v_type_4041_ = lean_ctor_get(v_toConstantVal_4037_, 2);
lean_inc_ref(v_type_4041_);
lean_dec_ref(v_toConstantVal_4037_);
v___x_4042_ = l_Lean_Meta_isPropFormerType(v_type_4041_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4078_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4045_ = v___x_4042_;
v_isShared_4046_ = v_isSharedCheck_4078_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4042_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4078_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
uint8_t v___x_4047_; 
v___x_4047_ = lean_unbox(v_a_4043_);
lean_dec(v_a_4043_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
lean_del_object(v___x_4045_);
lean_inc_n(v_indName_4015_, 2);
v___x_4048_ = l_Lean_mkRecName(v_indName_4015_);
v___x_4049_ = l_Lean_mkBRecOnName(v_indName_4015_);
lean_inc(v_all_4039_);
v___x_4050_ = lean_array_mk(v_all_4039_);
lean_inc(v___x_4049_);
lean_inc_ref(v___x_4050_);
lean_inc(v_numParams_4038_);
lean_inc(v___x_4048_);
v___x_4051_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4048_, v_numParams_4038_, v___x_4050_, v___x_4049_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4072_; 
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4072_ == 0)
{
lean_object* v_unused_4073_; 
v_unused_4073_ = lean_ctor_get(v___x_4051_, 0);
lean_dec(v_unused_4073_);
v___x_4053_ = v___x_4051_;
v_isShared_4054_ = v_isSharedCheck_4072_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v___x_4051_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4072_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = l_List_get_x21Internal___redArg(v___x_4025_, v_all_4039_, v___x_4055_);
lean_dec(v_all_4039_);
v___x_4057_ = lean_name_eq(v___x_4056_, v_indName_4015_);
lean_dec(v_indName_4015_);
lean_dec(v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
lean_dec_ref(v___x_4050_);
lean_dec(v___x_4049_);
lean_dec(v___x_4048_);
lean_dec(v_numNested_4040_);
lean_dec(v_numParams_4038_);
v___x_4058_ = lean_box(0);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v___x_4058_);
v___x_4060_ = v___x_4053_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
else
{
lean_object* v___x_4062_; lean_object* v___x_4063_; 
lean_del_object(v___x_4053_);
v___x_4062_ = lean_box(0);
v___x_4063_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4040_, v___x_4048_, v___x_4049_, v_numParams_4038_, v___x_4050_, v___x_4055_, v___x_4062_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_numNested_4040_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v___x_4063_, 0);
lean_dec(v_unused_4071_);
v___x_4065_ = v___x_4063_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_dec(v___x_4063_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 0, v___x_4062_);
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4062_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
else
{
return v___x_4063_;
}
}
}
}
else
{
lean_dec_ref(v___x_4050_);
lean_dec(v___x_4049_);
lean_dec(v___x_4048_);
lean_dec(v_numNested_4040_);
lean_dec(v_all_4039_);
lean_dec(v_numParams_4038_);
lean_dec(v_indName_4015_);
return v___x_4051_;
}
}
else
{
lean_object* v___x_4074_; lean_object* v___x_4076_; 
lean_dec(v_numNested_4040_);
lean_dec(v_all_4039_);
lean_dec(v_numParams_4038_);
lean_dec(v_indName_4015_);
v___x_4074_ = lean_box(0);
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4074_);
v___x_4076_ = v___x_4045_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_numNested_4040_);
lean_dec(v_all_4039_);
lean_dec(v_numParams_4038_);
lean_dec(v_indName_4015_);
v_a_4079_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4042_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4042_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
else
{
lean_object* v___x_4087_; lean_object* v___x_4089_; 
lean_dec(v_a_4027_);
lean_dec(v_indName_4015_);
v___x_4087_ = lean_box(0);
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4087_);
v___x_4089_ = v___x_4029_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4087_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_indName_4015_);
v_a_4092_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4026_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4026_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v___f_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v_a_4108_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v_a_4123_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v_a_4128_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v_a_4133_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v_a_4145_; lean_object* v___y_4148_; lean_object* v___y_4149_; lean_object* v_a_4150_; 
lean_inc(v_indName_4015_);
v___f_4100_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4100_, 0, v_indName_4015_);
v___x_4101_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4102_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4103_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4104_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4023_, v_options_4022_, v___x_4103_);
if (v___x_4104_ == 0)
{
lean_object* v___x_4219_; uint8_t v___x_4220_; 
v___x_4219_ = l_Lean_trace_profiler;
v___x_4220_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4022_, v___x_4219_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; 
lean_dec_ref(v___f_4100_);
lean_inc(v_indName_4015_);
v___x_4221_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4286_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4224_ = v___x_4221_;
v_isShared_4225_ = v_isSharedCheck_4286_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4286_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
if (lean_obj_tag(v_a_4222_) == 5)
{
lean_object* v_val_4226_; uint8_t v_isRec_4227_; 
v_val_4226_ = lean_ctor_get(v_a_4222_, 0);
lean_inc_ref(v_val_4226_);
lean_dec_ref_known(v_a_4222_, 1);
v_isRec_4227_ = lean_ctor_get_uint8(v_val_4226_, sizeof(void*)*6);
if (v_isRec_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4230_; 
lean_dec_ref(v_val_4226_);
lean_dec(v_indName_4015_);
v___x_4228_ = lean_box(0);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4228_);
v___x_4230_ = v___x_4224_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
else
{
lean_object* v_toConstantVal_4232_; lean_object* v_numParams_4233_; lean_object* v_all_4234_; lean_object* v_numNested_4235_; lean_object* v_type_4236_; lean_object* v___x_4237_; 
lean_del_object(v___x_4224_);
v_toConstantVal_4232_ = lean_ctor_get(v_val_4226_, 0);
lean_inc_ref(v_toConstantVal_4232_);
v_numParams_4233_ = lean_ctor_get(v_val_4226_, 1);
lean_inc(v_numParams_4233_);
v_all_4234_ = lean_ctor_get(v_val_4226_, 3);
lean_inc(v_all_4234_);
v_numNested_4235_ = lean_ctor_get(v_val_4226_, 5);
lean_inc(v_numNested_4235_);
lean_dec_ref(v_val_4226_);
v_type_4236_ = lean_ctor_get(v_toConstantVal_4232_, 2);
lean_inc_ref(v_type_4236_);
lean_dec_ref(v_toConstantVal_4232_);
v___x_4237_ = l_Lean_Meta_isPropFormerType(v_type_4236_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4273_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4273_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4273_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
uint8_t v___x_4242_; 
v___x_4242_ = lean_unbox(v_a_4238_);
lean_dec(v_a_4238_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_del_object(v___x_4240_);
lean_inc_n(v_indName_4015_, 2);
v___x_4243_ = l_Lean_mkRecName(v_indName_4015_);
v___x_4244_ = l_Lean_mkBRecOnName(v_indName_4015_);
lean_inc(v_all_4234_);
v___x_4245_ = lean_array_mk(v_all_4234_);
lean_inc(v___x_4244_);
lean_inc_ref(v___x_4245_);
lean_inc(v_numParams_4233_);
lean_inc(v___x_4243_);
v___x_4246_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4243_, v_numParams_4233_, v___x_4245_, v___x_4244_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4267_; 
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; 
v_unused_4268_ = lean_ctor_get(v___x_4246_, 0);
lean_dec(v_unused_4268_);
v___x_4248_ = v___x_4246_;
v_isShared_4249_ = v_isSharedCheck_4267_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v___x_4246_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4267_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v___x_4250_ = lean_unsigned_to_nat(0u);
v___x_4251_ = l_List_get_x21Internal___redArg(v___x_4025_, v_all_4234_, v___x_4250_);
lean_dec(v_all_4234_);
v___x_4252_ = lean_name_eq(v___x_4251_, v_indName_4015_);
lean_dec(v_indName_4015_);
lean_dec(v___x_4251_);
if (v___x_4252_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4255_; 
lean_dec_ref(v___x_4245_);
lean_dec(v___x_4244_);
lean_dec(v___x_4243_);
lean_dec(v_numNested_4235_);
lean_dec(v_numParams_4233_);
v___x_4253_ = lean_box(0);
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 0, v___x_4253_);
v___x_4255_ = v___x_4248_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v___x_4253_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_del_object(v___x_4248_);
v___x_4257_ = lean_box(0);
v___x_4258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4235_, v___x_4243_, v___x_4244_, v_numParams_4233_, v___x_4245_, v___x_4250_, v___x_4257_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_numNested_4235_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; 
v_unused_4266_ = lean_ctor_get(v___x_4258_, 0);
lean_dec(v_unused_4266_);
v___x_4260_ = v___x_4258_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_dec(v___x_4258_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4257_);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4257_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
else
{
return v___x_4258_;
}
}
}
}
else
{
lean_dec_ref(v___x_4245_);
lean_dec(v___x_4244_);
lean_dec(v___x_4243_);
lean_dec(v_numNested_4235_);
lean_dec(v_all_4234_);
lean_dec(v_numParams_4233_);
lean_dec(v_indName_4015_);
return v___x_4246_;
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4271_; 
lean_dec(v_numNested_4235_);
lean_dec(v_all_4234_);
lean_dec(v_numParams_4233_);
lean_dec(v_indName_4015_);
v___x_4269_ = lean_box(0);
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4269_);
v___x_4271_ = v___x_4240_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v_numNested_4235_);
lean_dec(v_all_4234_);
lean_dec(v_numParams_4233_);
lean_dec(v_indName_4015_);
v_a_4274_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4237_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4237_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
}
else
{
lean_object* v___x_4282_; lean_object* v___x_4284_; 
lean_dec(v_a_4222_);
lean_dec(v_indName_4015_);
v___x_4282_ = lean_box(0);
if (v_isShared_4225_ == 0)
{
lean_ctor_set(v___x_4224_, 0, v___x_4282_);
v___x_4284_ = v___x_4224_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v___x_4282_);
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
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_indName_4015_);
v_a_4287_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4221_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4221_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
else
{
goto v___jp_4152_;
}
}
else
{
goto v___jp_4152_;
}
v___jp_4105_:
{
lean_object* v___x_4109_; double v___x_4110_; double v___x_4111_; double v___x_4112_; double v___x_4113_; double v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4109_ = lean_io_mono_nanos_now();
v___x_4110_ = lean_float_of_nat(v___y_4107_);
v___x_4111_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4112_ = lean_float_div(v___x_4110_, v___x_4111_);
v___x_4113_ = lean_float_of_nat(v___x_4109_);
v___x_4114_ = lean_float_div(v___x_4113_, v___x_4111_);
v___x_4115_ = lean_box_float(v___x_4112_);
v___x_4116_ = lean_box_float(v___x_4114_);
v___x_4117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4115_);
lean_ctor_set(v___x_4117_, 1, v___x_4116_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v_a_4108_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4101_, v_hasTrace_4024_, v___x_4102_, v_options_4022_, v___x_4104_, v___y_4106_, v___f_4100_, v___x_4118_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4119_;
}
v___jp_4120_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4123_);
v___y_4106_ = v___y_4121_;
v___y_4107_ = v___y_4122_;
v_a_4108_ = v___x_4124_;
goto v___jp_4105_;
}
v___jp_4125_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_a_4128_);
v___y_4106_ = v___y_4126_;
v___y_4107_ = v___y_4127_;
v_a_4108_ = v___x_4129_;
goto v___jp_4105_;
}
v___jp_4130_:
{
lean_object* v___x_4134_; double v___x_4135_; double v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4134_ = lean_io_get_num_heartbeats();
v___x_4135_ = lean_float_of_nat(v___y_4132_);
v___x_4136_ = lean_float_of_nat(v___x_4134_);
v___x_4137_ = lean_box_float(v___x_4135_);
v___x_4138_ = lean_box_float(v___x_4136_);
v___x_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4137_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v_a_4133_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4101_, v_hasTrace_4024_, v___x_4102_, v_options_4022_, v___x_4104_, v___y_4131_, v___f_4100_, v___x_4140_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
return v___x_4141_;
}
v___jp_4142_:
{
lean_object* v___x_4146_; 
v___x_4146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_a_4145_);
v___y_4131_ = v___y_4143_;
v___y_4132_ = v___y_4144_;
v_a_4133_ = v___x_4146_;
goto v___jp_4130_;
}
v___jp_4147_:
{
lean_object* v___x_4151_; 
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_a_4150_);
v___y_4131_ = v___y_4148_;
v___y_4132_ = v___y_4149_;
v_a_4133_ = v___x_4151_;
goto v___jp_4130_;
}
v___jp_4152_:
{
lean_object* v___x_4153_; lean_object* v_a_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4153_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_4019_);
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref(v___x_4153_);
v___x_4155_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4156_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4022_, v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = lean_io_mono_nanos_now();
lean_inc(v_indName_4015_);
v___x_4158_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
if (lean_obj_tag(v_a_4159_) == 5)
{
lean_object* v_val_4160_; uint8_t v_isRec_4161_; 
v_val_4160_ = lean_ctor_get(v_a_4159_, 0);
lean_inc_ref(v_val_4160_);
lean_dec_ref_known(v_a_4159_, 1);
v_isRec_4161_ = lean_ctor_get_uint8(v_val_4160_, sizeof(void*)*6);
if (v_isRec_4161_ == 0)
{
lean_object* v___x_4162_; 
lean_dec_ref(v_val_4160_);
lean_dec(v_indName_4015_);
v___x_4162_ = lean_box(0);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v___x_4162_;
goto v___jp_4120_;
}
else
{
lean_object* v_toConstantVal_4163_; lean_object* v_numParams_4164_; lean_object* v_all_4165_; lean_object* v_numNested_4166_; lean_object* v_type_4167_; lean_object* v___x_4168_; 
v_toConstantVal_4163_ = lean_ctor_get(v_val_4160_, 0);
lean_inc_ref(v_toConstantVal_4163_);
v_numParams_4164_ = lean_ctor_get(v_val_4160_, 1);
lean_inc(v_numParams_4164_);
v_all_4165_ = lean_ctor_get(v_val_4160_, 3);
lean_inc(v_all_4165_);
v_numNested_4166_ = lean_ctor_get(v_val_4160_, 5);
lean_inc(v_numNested_4166_);
lean_dec_ref(v_val_4160_);
v_type_4167_ = lean_ctor_get(v_toConstantVal_4163_, 2);
lean_inc_ref(v_type_4167_);
lean_dec_ref(v_toConstantVal_4163_);
v___x_4168_ = l_Lean_Meta_isPropFormerType(v_type_4167_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; uint8_t v___x_4170_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = lean_unbox(v_a_4169_);
lean_dec(v_a_4169_);
if (v___x_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
lean_inc_n(v_indName_4015_, 2);
v___x_4171_ = l_Lean_mkRecName(v_indName_4015_);
v___x_4172_ = l_Lean_mkBRecOnName(v_indName_4015_);
lean_inc(v_all_4165_);
v___x_4173_ = lean_array_mk(v_all_4165_);
lean_inc(v___x_4172_);
lean_inc_ref(v___x_4173_);
lean_inc(v_numParams_4164_);
lean_inc(v___x_4171_);
v___x_4174_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4171_, v_numParams_4164_, v___x_4173_, v___x_4172_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
lean_dec_ref_known(v___x_4174_, 1);
v___x_4175_ = lean_unsigned_to_nat(0u);
v___x_4176_ = l_List_get_x21Internal___redArg(v___x_4025_, v_all_4165_, v___x_4175_);
lean_dec(v_all_4165_);
v___x_4177_ = lean_name_eq(v___x_4176_, v_indName_4015_);
lean_dec(v_indName_4015_);
lean_dec(v___x_4176_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
lean_dec_ref(v___x_4173_);
lean_dec(v___x_4172_);
lean_dec(v___x_4171_);
lean_dec(v_numNested_4166_);
lean_dec(v_numParams_4164_);
v___x_4178_ = lean_box(0);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v___x_4178_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_box(0);
v___x_4180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4166_, v___x_4171_, v___x_4172_, v_numParams_4164_, v___x_4173_, v___x_4175_, v___x_4179_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_numNested_4166_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_dec_ref_known(v___x_4180_, 1);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v___x_4179_;
goto v___jp_4120_;
}
else
{
lean_object* v_a_4181_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref_known(v___x_4180_, 1);
v___y_4126_ = v_a_4154_;
v___y_4127_ = v___x_4157_;
v_a_4128_ = v_a_4181_;
goto v___jp_4125_;
}
}
}
else
{
lean_dec_ref(v___x_4173_);
lean_dec(v___x_4172_);
lean_dec(v___x_4171_);
lean_dec(v_numNested_4166_);
lean_dec(v_all_4165_);
lean_dec(v_numParams_4164_);
lean_dec(v_indName_4015_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4182_; 
v_a_4182_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4174_, 1);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v_a_4182_;
goto v___jp_4120_;
}
else
{
lean_object* v_a_4183_; 
v_a_4183_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4174_, 1);
v___y_4126_ = v_a_4154_;
v___y_4127_ = v___x_4157_;
v_a_4128_ = v_a_4183_;
goto v___jp_4125_;
}
}
}
else
{
lean_object* v___x_4184_; 
lean_dec(v_numNested_4166_);
lean_dec(v_all_4165_);
lean_dec(v_numParams_4164_);
lean_dec(v_indName_4015_);
v___x_4184_ = lean_box(0);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v___x_4184_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4185_; 
lean_dec(v_numNested_4166_);
lean_dec(v_all_4165_);
lean_dec(v_numParams_4164_);
lean_dec(v_indName_4015_);
v_a_4185_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_4126_ = v_a_4154_;
v___y_4127_ = v___x_4157_;
v_a_4128_ = v_a_4185_;
goto v___jp_4125_;
}
}
}
else
{
lean_object* v___x_4186_; 
lean_dec(v_a_4159_);
lean_dec(v_indName_4015_);
v___x_4186_ = lean_box(0);
v___y_4121_ = v_a_4154_;
v___y_4122_ = v___x_4157_;
v_a_4123_ = v___x_4186_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4187_; 
lean_dec(v_indName_4015_);
v_a_4187_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4158_, 1);
v___y_4126_ = v_a_4154_;
v___y_4127_ = v___x_4157_;
v_a_4128_ = v_a_4187_;
goto v___jp_4125_;
}
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_4015_);
v___x_4189_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
if (lean_obj_tag(v_a_4190_) == 5)
{
lean_object* v_val_4191_; uint8_t v_isRec_4192_; 
v_val_4191_ = lean_ctor_get(v_a_4190_, 0);
lean_inc_ref(v_val_4191_);
lean_dec_ref_known(v_a_4190_, 1);
v_isRec_4192_ = lean_ctor_get_uint8(v_val_4191_, sizeof(void*)*6);
if (v_isRec_4192_ == 0)
{
lean_object* v___x_4193_; 
lean_dec_ref(v_val_4191_);
lean_dec(v_indName_4015_);
v___x_4193_ = lean_box(0);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v___x_4193_;
goto v___jp_4142_;
}
else
{
lean_object* v_toConstantVal_4194_; lean_object* v_numParams_4195_; lean_object* v_all_4196_; lean_object* v_numNested_4197_; lean_object* v_type_4198_; lean_object* v___x_4199_; 
v_toConstantVal_4194_ = lean_ctor_get(v_val_4191_, 0);
lean_inc_ref(v_toConstantVal_4194_);
v_numParams_4195_ = lean_ctor_get(v_val_4191_, 1);
lean_inc(v_numParams_4195_);
v_all_4196_ = lean_ctor_get(v_val_4191_, 3);
lean_inc(v_all_4196_);
v_numNested_4197_ = lean_ctor_get(v_val_4191_, 5);
lean_inc(v_numNested_4197_);
lean_dec_ref(v_val_4191_);
v_type_4198_ = lean_ctor_get(v_toConstantVal_4194_, 2);
lean_inc_ref(v_type_4198_);
lean_dec_ref(v_toConstantVal_4194_);
v___x_4199_ = l_Lean_Meta_isPropFormerType(v_type_4198_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; uint8_t v___x_4201_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = lean_unbox(v_a_4200_);
lean_dec(v_a_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_inc_n(v_indName_4015_, 2);
v___x_4202_ = l_Lean_mkRecName(v_indName_4015_);
v___x_4203_ = l_Lean_mkBRecOnName(v_indName_4015_);
lean_inc(v_all_4196_);
v___x_4204_ = lean_array_mk(v_all_4196_);
lean_inc(v___x_4203_);
lean_inc_ref(v___x_4204_);
lean_inc(v_numParams_4195_);
lean_inc(v___x_4202_);
v___x_4205_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4202_, v_numParams_4195_, v___x_4204_, v___x_4203_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
lean_dec_ref_known(v___x_4205_, 1);
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = l_List_get_x21Internal___redArg(v___x_4025_, v_all_4196_, v___x_4206_);
lean_dec(v_all_4196_);
v___x_4208_ = lean_name_eq(v___x_4207_, v_indName_4015_);
lean_dec(v_indName_4015_);
lean_dec(v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; 
lean_dec_ref(v___x_4204_);
lean_dec(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec(v_numNested_4197_);
lean_dec(v_numParams_4195_);
v___x_4209_ = lean_box(0);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v___x_4209_;
goto v___jp_4142_;
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = lean_box(0);
v___x_4211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4197_, v___x_4202_, v___x_4203_, v_numParams_4195_, v___x_4204_, v___x_4206_, v___x_4210_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_numNested_4197_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_dec_ref_known(v___x_4211_, 1);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v___x_4210_;
goto v___jp_4142_;
}
else
{
lean_object* v_a_4212_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v___y_4148_ = v_a_4154_;
v___y_4149_ = v___x_4188_;
v_a_4150_ = v_a_4212_;
goto v___jp_4147_;
}
}
}
else
{
lean_dec_ref(v___x_4204_);
lean_dec(v___x_4203_);
lean_dec(v___x_4202_);
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_4015_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4213_; 
v_a_4213_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4205_, 1);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v_a_4213_;
goto v___jp_4142_;
}
else
{
lean_object* v_a_4214_; 
v_a_4214_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4205_, 1);
v___y_4148_ = v_a_4154_;
v___y_4149_ = v___x_4188_;
v_a_4150_ = v_a_4214_;
goto v___jp_4147_;
}
}
}
else
{
lean_object* v___x_4215_; 
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_4015_);
v___x_4215_ = lean_box(0);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v___x_4215_;
goto v___jp_4142_;
}
}
else
{
lean_object* v_a_4216_; 
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_4015_);
v_a_4216_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4199_, 1);
v___y_4148_ = v_a_4154_;
v___y_4149_ = v___x_4188_;
v_a_4150_ = v_a_4216_;
goto v___jp_4147_;
}
}
}
else
{
lean_object* v___x_4217_; 
lean_dec(v_a_4190_);
lean_dec(v_indName_4015_);
v___x_4217_ = lean_box(0);
v___y_4143_ = v_a_4154_;
v___y_4144_ = v___x_4188_;
v_a_4145_ = v___x_4217_;
goto v___jp_4142_;
}
}
else
{
lean_object* v_a_4218_; 
lean_dec(v_indName_4015_);
v_a_4218_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4148_ = v_a_4154_;
v___y_4149_ = v___x_4188_;
v_a_4150_ = v_a_4218_;
goto v___jp_4147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_mkBRecOn(v_indName_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v_inst_4307_, lean_object* v_R_4308_, lean_object* v_a_4309_, lean_object* v_b_4310_, lean_object* v_c_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v___x_4317_; 
v___x_4317_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4302_, v___x_4303_, v___x_4304_, v___x_4305_, v___x_4306_, v_a_4309_, v_b_4310_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4318_, lean_object* v___x_4319_, lean_object* v___x_4320_, lean_object* v___x_4321_, lean_object* v___x_4322_, lean_object* v_inst_4323_, lean_object* v_R_4324_, lean_object* v_a_4325_, lean_object* v_b_4326_, lean_object* v_c_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4318_, v___x_4319_, v___x_4320_, v___x_4321_, v___x_4322_, v_inst_4323_, v_R_4324_, v_a_4325_, v_b_4326_, v_c_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_);
lean_dec(v___y_4331_);
lean_dec_ref(v___y_4330_);
lean_dec(v___y_4329_);
lean_dec_ref(v___y_4328_);
lean_dec(v_upperBound_4318_);
return v_res_4333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4379_ = lean_unsigned_to_nat(2304625798u);
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4381_ = l_Lean_Name_num___override(v___x_4380_, v___x_4379_);
return v___x_4381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4383_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4384_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4385_ = l_Lean_Name_str___override(v___x_4384_, v___x_4383_);
return v___x_4385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4388_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4389_ = l_Lean_Name_str___override(v___x_4388_, v___x_4387_);
return v___x_4389_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_unsigned_to_nat(2u);
v___x_4391_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4392_ = l_Lean_Name_num___override(v___x_4391_, v___x_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4394_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4395_ = 0;
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4397_ = l_Lean_registerTraceClass(v___x_4394_, v___x_4395_, v___x_4396_);
return v___x_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4399_;
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
