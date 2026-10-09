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
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = 0;
v___x_30_ = lean_box(0);
v___x_31_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_29_, v___x_30_, v_type_20_, v___f_28_, v_cleanupAnnotations_22_, v___x_29_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_31_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_31_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_20_ = stack[0].m_obj;
lean_object* v_k_21_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_22_ = stack[2].m_num;
lean_object* v___y_23_ = stack[3].m_obj;
lean_object* v___y_24_ = stack[4].m_obj;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_20_, v_k_21_, v_cleanupAnnotations_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___boxed(lean_object* v_type_49_, lean_object* v_k_50_, lean_object* v_cleanupAnnotations_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; lean_object* v_res_58_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_51_);
v_res_58_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_49_, v_k_50_, v_cleanupAnnotations_boxed_57_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_58_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(lean_object* v_00_u03b1_59_, lean_object* v_type_60_, lean_object* v_k_61_, uint8_t v_cleanupAnnotations_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_60_ = stack[1].m_obj;
lean_object* v_k_61_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_62_ = stack[3].m_num;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v___y_66_ = stack[7].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(lean_box(0), v_type_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___boxed(lean_object* v_00_u03b1_70_, lean_object* v_type_71_, lean_object* v_k_72_, lean_object* v_cleanupAnnotations_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; lean_object* v_res_80_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_73_);
v_res_80_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1(v_00_u03b1_70_, v_type_71_, v_k_72_, v_cleanupAnnotations_boxed_79_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_80_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(lean_object* v_rlvl_81_, uint8_t v___x_82_, lean_object* v_args_83_, lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; 
v___x_90_ = l_Lean_Expr_sort___override(v_rlvl_81_);
v___x_91_ = 0;
v___x_92_ = 1;
v___x_93_ = l_Lean_Meta_mkForallFVars(v_args_83_, v___x_90_, v___x_91_, v___x_82_, v___x_82_, v___x_92_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
return v___x_93_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_81_ = stack[0].m_obj;
uint8_t v___x_82_ = stack[1].m_num;
lean_object* v_args_83_ = stack[2].m_obj;
lean_object* v_x_84_ = stack[3].m_obj;
lean_object* v___y_85_ = stack[4].m_obj;
lean_object* v___y_86_ = stack[5].m_obj;
lean_object* v___y_87_ = stack[6].m_obj;
lean_object* v___y_88_ = stack[7].m_obj;
lean_object* v_res_94_;
v_res_94_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_81_, v___x_82_, v_args_83_, v_x_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
stack->m_obj
 = v_res_94_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed(lean_object* v_rlvl_95_, lean_object* v___x_96_, lean_object* v_args_97_, lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
uint8_t v___x_1927__boxed_104_; lean_object* v_res_105_; 
v___x_1927__boxed_104_ = lean_unbox(v___x_96_);
v_res_105_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_95_, v___x_1927__boxed_104_, v_args_97_, v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_args_97_);
return v_res_105_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(lean_object* v_k_106_, lean_object* v_b_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; 
lean_inc(v___y_111_);
lean_inc_ref(v___y_110_);
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
v___x_113_ = lean_apply_6(v_k_106_, v_b_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, lean_box(0));
return v___x_113_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_106_ = stack[0].m_obj;
lean_object* v_b_107_ = stack[1].m_obj;
lean_object* v___y_108_ = stack[2].m_obj;
lean_object* v___y_109_ = stack[3].m_obj;
lean_object* v___y_110_ = stack[4].m_obj;
lean_object* v___y_111_ = stack[5].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(v_k_106_, v_b_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(v_k_115_, v_b_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(lean_object* v_name_123_, uint8_t v_bi_124_, lean_object* v_type_125_, lean_object* v_k_126_, uint8_t v_kind_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___f_133_; lean_object* v___x_134_; 
v___f_133_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_133_, 0, v_k_126_);
v___x_134_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_123_, v_bi_124_, v_type_125_, v___f_133_, v_kind_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_a_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_134_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_134_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_123_ = stack[0].m_obj;
uint8_t v_bi_124_ = stack[1].m_num;
lean_object* v_type_125_ = stack[2].m_obj;
lean_object* v_k_126_ = stack[3].m_obj;
uint8_t v_kind_127_ = stack[4].m_num;
lean_object* v___y_128_ = stack[5].m_obj;
lean_object* v___y_129_ = stack[6].m_obj;
lean_object* v___y_130_ = stack[7].m_obj;
lean_object* v___y_131_ = stack[8].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_123_, v_bi_124_, v_type_125_, v_k_126_, v_kind_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___boxed(lean_object* v_name_152_, lean_object* v_bi_153_, lean_object* v_type_154_, lean_object* v_k_155_, lean_object* v_kind_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_bi_boxed_162_; uint8_t v_kind_boxed_163_; lean_object* v_res_164_; 
v_bi_boxed_162_ = lean_unbox(v_bi_153_);
v_kind_boxed_163_ = lean_unbox(v_kind_156_);
v_res_164_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_152_, v_bi_boxed_162_, v_type_154_, v_k_155_, v_kind_boxed_163_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_164_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(lean_object* v_name_165_, lean_object* v_type_166_, lean_object* v_k_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; 
v___x_173_ = 0;
v___x_174_ = 0;
v___x_175_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_165_, v___x_173_, v_type_166_, v_k_167_, v___x_174_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
return v___x_175_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_165_ = stack[0].m_obj;
lean_object* v_type_166_ = stack[1].m_obj;
lean_object* v_k_167_ = stack[2].m_obj;
lean_object* v___y_168_ = stack[3].m_obj;
lean_object* v___y_169_ = stack[4].m_obj;
lean_object* v___y_170_ = stack[5].m_obj;
lean_object* v___y_171_ = stack[6].m_obj;
lean_object* v_res_176_;
v_res_176_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_name_165_, v_type_166_, v_k_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg___boxed(lean_object* v_name_177_, lean_object* v_type_178_, lean_object* v_k_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_name_177_, v_type_178_, v_k_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_185_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(lean_object* v_a_186_, lean_object* v_as_187_, size_t v_i_188_, size_t v_stop_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_188_, v_stop_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_array_uget_borrowed(v_as_187_, v_i_188_);
v___x_192_ = lean_expr_eqv(v_a_186_, v___x_191_);
if (v___x_192_ == 0)
{
size_t v___x_193_; size_t v___x_194_; 
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_188_, v___x_193_);
v_i_188_ = v___x_194_;
goto _start;
}
else
{
return v___x_192_;
}
}
else
{
uint8_t v___x_196_; 
v___x_196_ = 0;
return v___x_196_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_186_ = stack[0].m_obj;
lean_object* v_as_187_ = stack[1].m_obj;
size_t v_i_188_ = stack[2].m_num;
size_t v_stop_189_ = stack[3].m_num;
uint8_t v_res_197_;
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_186_, v_as_187_, v_i_188_, v_stop_189_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_a_198_, lean_object* v_as_199_, lean_object* v_i_200_, lean_object* v_stop_201_){
_start:
{
size_t v_i_boxed_202_; size_t v_stop_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_i_boxed_202_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_stop_boxed_203_ = lean_unbox_usize(v_stop_201_);
lean_dec(v_stop_201_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_198_, v_as_199_, v_i_boxed_202_, v_stop_boxed_203_);
lean_dec_ref(v_as_199_);
lean_dec_ref(v_a_198_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(lean_object* v_as_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_array_get_size(v_as_206_);
v___x_210_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
return v___x_210_;
}
else
{
if (v___x_210_ == 0)
{
return v___x_210_;
}
else
{
size_t v___x_211_; size_t v___x_212_; uint8_t v___x_213_; 
v___x_211_ = ((size_t)0ULL);
v___x_212_ = lean_usize_of_nat(v___x_209_);
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_207_, v_as_206_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_206_ = stack[0].m_obj;
lean_object* v_a_207_ = stack[1].m_obj;
uint8_t v_res_214_;
v_res_214_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(v_as_206_, v_a_207_);
stack->m_num = v_res_214_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0___boxed(lean_object* v_as_215_, lean_object* v_a_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(v_as_215_, v_a_216_);
lean_dec_ref(v_a_216_);
lean_dec_ref(v_as_215_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(lean_object* v_arg__args_219_, lean_object* v_arg__type_220_, uint8_t v___x_221_, uint8_t v___x_222_, lean_object* v_prods_223_, lean_object* v_rlvl_224_, lean_object* v_motives_225_, lean_object* v_tail_226_, lean_object* v_arg_x27_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v_arg_x27_227_);
v___x_233_ = l_Lean_mkAppN(v_arg_x27_227_, v_arg__args_219_);
v___x_234_ = l_Lean_Meta_mkPProd(v_arg__type_220_, v___x_233_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_a_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = 1;
v___x_237_ = l_Lean_Meta_mkForallFVars(v_arg__args_219_, v_a_235_, v___x_221_, v___x_222_, v___x_222_, v___x_236_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = lean_array_push(v_prods_223_, v_a_238_);
v___x_240_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_224_, v_motives_225_, v___x_239_, v_tail_226_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_a_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_mk_empty_array_with_capacity(v___x_242_);
v___x_244_ = lean_array_push(v___x_243_, v_arg_x27_227_);
v___x_245_ = l_Lean_Meta_mkLambdaFVars(v___x_244_, v_a_241_, v___x_221_, v___x_222_, v___x_221_, v___x_222_, v___x_236_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec_ref(v___x_244_);
return v___x_245_;
}
else
{
lean_dec_ref(v_arg_x27_227_);
return v___x_240_;
}
}
else
{
lean_dec_ref(v_arg_x27_227_);
lean_dec(v_tail_226_);
lean_dec_ref(v_motives_225_);
lean_dec(v_rlvl_224_);
lean_dec_ref(v_prods_223_);
return v___x_237_;
}
}
else
{
lean_dec_ref(v_arg_x27_227_);
lean_dec(v_tail_226_);
lean_dec_ref(v_motives_225_);
lean_dec(v_rlvl_224_);
lean_dec_ref(v_prods_223_);
return v___x_234_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg__args_219_ = stack[0].m_obj;
lean_object* v_arg__type_220_ = stack[1].m_obj;
uint8_t v___x_221_ = stack[2].m_num;
uint8_t v___x_222_ = stack[3].m_num;
lean_object* v_prods_223_ = stack[4].m_obj;
lean_object* v_rlvl_224_ = stack[5].m_obj;
lean_object* v_motives_225_ = stack[6].m_obj;
lean_object* v_tail_226_ = stack[7].m_obj;
lean_object* v_arg_x27_227_ = stack[8].m_obj;
lean_object* v___y_228_ = stack[9].m_obj;
lean_object* v___y_229_ = stack[10].m_obj;
lean_object* v___y_230_ = stack[11].m_obj;
lean_object* v___y_231_ = stack[12].m_obj;
lean_object* v_res_246_;
v_res_246_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_219_, v_arg__type_220_, v___x_221_, v___x_222_, v_prods_223_, v_rlvl_224_, v_motives_225_, v_tail_226_, v_arg_x27_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
stack->m_obj
 = v_res_246_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed(lean_object* v_arg__args_247_, lean_object* v_arg__type_248_, lean_object* v___x_249_, lean_object* v___x_250_, lean_object* v_prods_251_, lean_object* v_rlvl_252_, lean_object* v_motives_253_, lean_object* v_tail_254_, lean_object* v_arg_x27_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
uint8_t v___x_2165__boxed_261_; uint8_t v___x_2166__boxed_262_; lean_object* v_res_263_; 
v___x_2165__boxed_261_ = lean_unbox(v___x_249_);
v___x_2166__boxed_262_ = lean_unbox(v___x_250_);
v_res_263_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_247_, v_arg__type_248_, v___x_2165__boxed_261_, v___x_2166__boxed_262_, v_prods_251_, v_rlvl_252_, v_motives_253_, v_tail_254_, v_arg_x27_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec_ref(v_arg__args_247_);
return v_res_263_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(lean_object* v_motives_264_, lean_object* v_rlvl_265_, lean_object* v_prods_266_, lean_object* v_tail_267_, lean_object* v_head_268_, lean_object* v_a_269_, lean_object* v_arg__args_270_, lean_object* v_arg__type_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; uint8_t v___x_279_; 
v___x_277_ = l_Lean_Expr_getAppFn(v_arg__type_271_);
v___x_278_ = l_Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0(v_motives_264_, v___x_277_);
lean_dec_ref(v___x_277_);
v___x_279_ = 1;
if (v___x_278_ == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_arg__type_271_);
lean_dec_ref(v_arg__args_270_);
lean_dec_ref(v_a_269_);
v___x_280_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_265_, v_motives_264_, v_prods_266_, v_tail_267_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_mk_empty_array_with_capacity(v___x_282_);
v___x_284_ = lean_array_push(v___x_283_, v_head_268_);
v___x_285_ = 1;
v___x_286_ = l_Lean_Meta_mkLambdaFVars(v___x_284_, v_a_281_, v___x_278_, v___x_279_, v___x_278_, v___x_279_, v___x_285_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec_ref(v___x_284_);
return v___x_286_;
}
else
{
lean_dec_ref(v_head_268_);
return v___x_280_;
}
}
else
{
lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_box(v___x_279_);
lean_inc(v_rlvl_265_);
v___f_288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_288_, 0, v_rlvl_265_);
lean_closure_set(v___f_288_, 1, v___x_287_);
v___x_289_ = l_Lean_Expr_fvarId_x21(v_head_268_);
lean_dec_ref(v_head_268_);
v___x_290_ = l_Lean_FVarId_getUserName___redArg(v___x_289_, v___y_272_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
v___x_292_ = 0;
v___x_293_ = lean_box(v___x_292_);
v___x_294_ = lean_box(v___x_279_);
v___f_295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_295_, 0, v_arg__args_270_);
lean_closure_set(v___f_295_, 1, v_arg__type_271_);
lean_closure_set(v___f_295_, 2, v___x_293_);
lean_closure_set(v___f_295_, 3, v___x_294_);
lean_closure_set(v___f_295_, 4, v_prods_266_);
lean_closure_set(v___f_295_, 5, v_rlvl_265_);
lean_closure_set(v___f_295_, 6, v_motives_264_);
lean_closure_set(v___f_295_, 7, v_tail_267_);
v___x_296_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_269_, v___f_288_, v___x_292_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_291_, v_a_297_, v___f_295_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
return v___x_298_;
}
else
{
lean_dec_ref(v___f_295_);
lean_dec(v_a_291_);
return v___x_296_;
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v___f_288_);
lean_dec_ref(v_arg__type_271_);
lean_dec_ref(v_arg__args_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_tail_267_);
lean_dec_ref(v_prods_266_);
lean_dec(v_rlvl_265_);
lean_dec_ref(v_motives_264_);
v_a_299_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_290_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_290_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_motives_264_ = stack[0].m_obj;
lean_object* v_rlvl_265_ = stack[1].m_obj;
lean_object* v_prods_266_ = stack[2].m_obj;
lean_object* v_tail_267_ = stack[3].m_obj;
lean_object* v_head_268_ = stack[4].m_obj;
lean_object* v_a_269_ = stack[5].m_obj;
lean_object* v_arg__args_270_ = stack[6].m_obj;
lean_object* v_arg__type_271_ = stack[7].m_obj;
lean_object* v___y_272_ = stack[8].m_obj;
lean_object* v___y_273_ = stack[9].m_obj;
lean_object* v___y_274_ = stack[10].m_obj;
lean_object* v___y_275_ = stack[11].m_obj;
lean_object* v_res_307_;
v_res_307_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(v_motives_264_, v_rlvl_265_, v_prods_266_, v_tail_267_, v_head_268_, v_a_269_, v_arg__args_270_, v_arg__type_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2___boxed(lean_object* v_motives_308_, lean_object* v_rlvl_309_, lean_object* v_prods_310_, lean_object* v_tail_311_, lean_object* v_head_312_, lean_object* v_a_313_, lean_object* v_arg__args_314_, lean_object* v_arg__type_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2(v_motives_308_, v_rlvl_309_, v_prods_310_, v_tail_311_, v_head_312_, v_a_313_, v_arg__args_314_, v_arg__type_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(lean_object* v_rlvl_322_, lean_object* v_motives_323_, lean_object* v_prods_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
if (lean_obj_tag(v_a_325_) == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v_motives_323_);
v___x_331_ = l_Lean_Meta_PProdN_pack(v_rlvl_322_, v_prods_324_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_331_;
}
else
{
lean_object* v_head_332_; lean_object* v_tail_333_; lean_object* v___x_334_; 
v_head_332_ = lean_ctor_get(v_a_325_, 0);
lean_inc_n(v_head_332_, 2);
v_tail_333_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_tail_333_);
lean_dec_ref_known(v_a_325_, 2);
lean_inc(v_a_329_);
lean_inc_ref(v_a_328_);
lean_inc(v_a_327_);
lean_inc_ref(v_a_326_);
v___x_334_ = lean_infer_type(v_head_332_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___f_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_n(v_a_335_, 2);
lean_dec_ref_known(v___x_334_, 1);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__2___boxed), 13, 6);
lean_closure_set(v___f_336_, 0, v_motives_323_);
lean_closure_set(v___f_336_, 1, v_rlvl_322_);
lean_closure_set(v___f_336_, 2, v_prods_324_);
lean_closure_set(v___f_336_, 3, v_tail_333_);
lean_closure_set(v___f_336_, 4, v_head_332_);
lean_closure_set(v___f_336_, 5, v_a_335_);
v___x_337_ = 0;
v___x_338_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_335_, v___f_336_, v___x_337_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
return v___x_338_;
}
else
{
lean_dec(v_tail_333_);
lean_dec(v_head_332_);
lean_dec_ref(v_prods_324_);
lean_dec_ref(v_motives_323_);
lean_dec(v_rlvl_322_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_322_ = stack[0].m_obj;
lean_object* v_motives_323_ = stack[1].m_obj;
lean_object* v_prods_324_ = stack[2].m_obj;
lean_object* v_a_325_ = stack[3].m_obj;
lean_object* v_a_326_ = stack[4].m_obj;
lean_object* v_a_327_ = stack[5].m_obj;
lean_object* v_a_328_ = stack[6].m_obj;
lean_object* v_a_329_ = stack[7].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_322_, v_motives_323_, v_prods_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___boxed(lean_object* v_rlvl_340_, lean_object* v_motives_341_, lean_object* v_prods_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_340_, v_motives_341_, v_prods_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
lean_dec(v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(lean_object* v_00_u03b1_350_, lean_object* v_name_351_, uint8_t v_bi_352_, lean_object* v_type_353_, lean_object* v_k_354_, uint8_t v_kind_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg(v_name_351_, v_bi_352_, v_type_353_, v_k_354_, v_kind_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_351_ = stack[1].m_obj;
uint8_t v_bi_352_ = stack[2].m_num;
lean_object* v_type_353_ = stack[3].m_obj;
lean_object* v_k_354_ = stack[4].m_obj;
uint8_t v_kind_355_ = stack[5].m_num;
lean_object* v___y_356_ = stack[6].m_obj;
lean_object* v___y_357_ = stack[7].m_obj;
lean_object* v___y_358_ = stack[8].m_obj;
lean_object* v___y_359_ = stack[9].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(lean_box(0), v_name_351_, v_bi_352_, v_type_353_, v_k_354_, v_kind_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_363_, lean_object* v_name_364_, lean_object* v_bi_365_, lean_object* v_type_366_, lean_object* v_k_367_, lean_object* v_kind_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v_bi_boxed_374_; uint8_t v_kind_boxed_375_; lean_object* v_res_376_; 
v_bi_boxed_374_ = lean_unbox(v_bi_365_);
v_kind_boxed_375_ = lean_unbox(v_kind_368_);
v_res_376_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3(v_00_u03b1_363_, v_name_364_, v_bi_boxed_374_, v_type_366_, v_k_367_, v_kind_boxed_375_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_376_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(lean_object* v_00_u03b1_377_, lean_object* v_name_378_, lean_object* v_type_379_, lean_object* v_k_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_name_378_, v_type_379_, v_k_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_378_ = stack[1].m_obj;
lean_object* v_type_379_ = stack[2].m_obj;
lean_object* v_k_380_ = stack[3].m_obj;
lean_object* v___y_381_ = stack[4].m_obj;
lean_object* v___y_382_ = stack[5].m_obj;
lean_object* v___y_383_ = stack[6].m_obj;
lean_object* v___y_384_ = stack[7].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(lean_box(0), v_name_378_, v_type_379_, v_k_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___boxed(lean_object* v_00_u03b1_388_, lean_object* v_name_389_, lean_object* v_type_390_, lean_object* v_k_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2(v_00_u03b1_388_, v_name_389_, v_type_390_, v_k_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(lean_object* v_rlvl_400_, lean_object* v_motives_401_, lean_object* v_minor__args_402_, lean_object* v_x_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_410_ = lean_array_to_list(v_minor__args_402_);
v___x_411_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_400_, v_motives_401_, v___x_409_, v___x_410_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
return v___x_411_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_400_ = stack[0].m_obj;
lean_object* v_motives_401_ = stack[1].m_obj;
lean_object* v_minor__args_402_ = stack[2].m_obj;
lean_object* v_x_403_ = stack[3].m_obj;
lean_object* v___y_404_ = stack[4].m_obj;
lean_object* v___y_405_ = stack[5].m_obj;
lean_object* v___y_406_ = stack[6].m_obj;
lean_object* v___y_407_ = stack[7].m_obj;
lean_object* v_res_412_;
v_res_412_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(v_rlvl_400_, v_motives_401_, v_minor__args_402_, v_x_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___boxed(lean_object* v_rlvl_413_, lean_object* v_motives_414_, lean_object* v_minor__args_415_, lean_object* v_x_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0(v_rlvl_413_, v_motives_414_, v_minor__args_415_, v_x_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec_ref(v_x_416_);
return v_res_422_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(lean_object* v_rlvl_423_, lean_object* v_motives_424_, lean_object* v_minorType_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___f_431_; uint8_t v___x_432_; lean_object* v___x_433_; 
v___f_431_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___boxed), 9, 2);
lean_closure_set(v___f_431_, 0, v_rlvl_423_);
lean_closure_set(v___f_431_, 1, v_motives_424_);
v___x_432_ = 0;
v___x_433_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_425_, v___f_431_, v___x_432_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
return v___x_433_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_423_ = stack[0].m_obj;
lean_object* v_motives_424_ = stack[1].m_obj;
lean_object* v_minorType_425_ = stack[2].m_obj;
lean_object* v_a_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
lean_object* v_a_428_ = stack[5].m_obj;
lean_object* v_a_429_ = stack[6].m_obj;
lean_object* v_res_434_;
v_res_434_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v_rlvl_423_, v_motives_424_, v_minorType_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___boxed(lean_object* v_rlvl_435_, lean_object* v_motives_436_, lean_object* v_minorType_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v_rlvl_435_, v_motives_436_, v_minorType_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_443_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___f_451_; lean_object* v___x_4921__overap_452_; lean_object* v___x_453_; 
v___f_451_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_4921__overap_452_ = lean_panic_fn_borrowed(v___f_451_, v_msg_445_);
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
lean_inc(v___y_447_);
lean_inc_ref(v___y_446_);
v___x_453_ = lean_apply_5(v___x_4921__overap_452_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, lean_box(0));
return v___x_453_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_445_ = stack[0].m_obj;
lean_object* v___y_446_ = stack[1].m_obj;
lean_object* v___y_447_ = stack[2].m_obj;
lean_object* v___y_448_ = stack[3].m_obj;
lean_object* v___y_449_ = stack[4].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v_msg_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___boxed(lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v_msg_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_461_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(lean_object* v_name_462_, lean_object* v_levelParams_463_, lean_object* v_type_464_, lean_object* v_value_465_, lean_object* v_hints_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; uint8_t v___y_471_; uint8_t v___y_478_; lean_object* v_env_481_; uint8_t v___x_482_; 
v___x_469_ = lean_st_ref_get(v___y_467_);
v_env_481_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref_n(v_env_481_, 2);
lean_dec(v___x_469_);
v___x_482_ = l_Lean_Environment_hasUnsafe(v_env_481_, v_type_464_);
if (v___x_482_ == 0)
{
uint8_t v___x_483_; 
v___x_483_ = l_Lean_Environment_hasUnsafe(v_env_481_, v_value_465_);
v___y_478_ = v___x_483_;
goto v___jp_477_;
}
else
{
lean_dec_ref(v_env_481_);
v___y_478_ = v___x_482_;
goto v___jp_477_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc(v_name_462_);
v___x_472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_472_, 0, v_name_462_);
lean_ctor_set(v___x_472_, 1, v_levelParams_463_);
lean_ctor_set(v___x_472_, 2, v_type_464_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v_name_462_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v_value_465_);
lean_ctor_set(v___x_475_, 2, v_hints_466_);
lean_ctor_set(v___x_475_, 3, v___x_474_);
lean_ctor_set_uint8(v___x_475_, sizeof(void*)*4, v___y_471_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
uint8_t v___x_479_; 
v___x_479_ = 1;
v___y_471_ = v___x_479_;
goto v___jp_470_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = 0;
v___y_471_ = v___x_480_;
goto v___jp_470_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_462_ = stack[0].m_obj;
lean_object* v_levelParams_463_ = stack[1].m_obj;
lean_object* v_type_464_ = stack[2].m_obj;
lean_object* v_value_465_ = stack[3].m_obj;
lean_object* v_hints_466_ = stack[4].m_obj;
lean_object* v___y_467_ = stack[5].m_obj;
lean_object* v_res_484_;
v_res_484_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_462_, v_levelParams_463_, v_type_464_, v_value_465_, v_hints_466_, v___y_467_);
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg___boxed(lean_object* v_name_485_, lean_object* v_levelParams_486_, lean_object* v_type_487_, lean_object* v_value_488_, lean_object* v_hints_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_485_, v_levelParams_486_, v_type_487_, v_value_488_, v_hints_489_, v___y_490_);
lean_dec(v___y_490_);
return v_res_492_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(lean_object* v_name_493_, lean_object* v_levelParams_494_, lean_object* v_type_495_, lean_object* v_value_496_, lean_object* v_hints_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_493_, v_levelParams_494_, v_type_495_, v_value_496_, v_hints_497_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_493_ = stack[0].m_obj;
lean_object* v_levelParams_494_ = stack[1].m_obj;
lean_object* v_type_495_ = stack[2].m_obj;
lean_object* v_value_496_ = stack[3].m_obj;
lean_object* v_hints_497_ = stack[4].m_obj;
lean_object* v___y_498_ = stack[5].m_obj;
lean_object* v___y_499_ = stack[6].m_obj;
lean_object* v___y_500_ = stack[7].m_obj;
lean_object* v___y_501_ = stack[8].m_obj;
lean_object* v_res_504_;
v_res_504_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(v_name_493_, v_levelParams_494_, v_type_495_, v_value_496_, v_hints_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___boxed(lean_object* v_name_505_, lean_object* v_levelParams_506_, lean_object* v_type_507_, lean_object* v_value_508_, lean_object* v_hints_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(v_name_505_, v_levelParams_506_, v_type_507_, v_value_508_, v_hints_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_515_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(lean_object* v___x_516_, lean_object* v___x_517_, lean_object* v_as_518_, size_t v_sz_519_, size_t v_i_520_, lean_object* v_b_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_520_, v_sz_519_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
lean_dec_ref(v___x_517_);
lean_dec(v___x_516_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_b_521_);
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_array_uget_borrowed(v_as_518_, v_i_520_);
lean_inc(v___y_525_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_523_);
lean_inc_ref(v___y_522_);
lean_inc(v_a_529_);
v___x_530_ = lean_infer_type(v_a_529_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
lean_inc_ref(v___x_517_);
lean_inc(v___x_516_);
v___x_532_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v___x_516_, v___x_517_, v_a_531_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; size_t v___x_535_; size_t v___x_536_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = l_Lean_Expr_app___override(v_b_521_, v_a_533_);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_add(v_i_520_, v___x_535_);
v_i_520_ = v___x_536_;
v_b_521_ = v___x_534_;
goto _start;
}
else
{
lean_dec_ref(v_b_521_);
lean_dec_ref(v___x_517_);
lean_dec(v___x_516_);
return v___x_532_;
}
}
else
{
lean_dec_ref(v_b_521_);
lean_dec_ref(v___x_517_);
lean_dec(v___x_516_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_516_ = stack[0].m_obj;
lean_object* v___x_517_ = stack[1].m_obj;
lean_object* v_as_518_ = stack[2].m_obj;
size_t v_sz_519_ = stack[3].m_num;
size_t v_i_520_ = stack[4].m_num;
lean_object* v_b_521_ = stack[5].m_obj;
lean_object* v___y_522_ = stack[6].m_obj;
lean_object* v___y_523_ = stack[7].m_obj;
lean_object* v___y_524_ = stack[8].m_obj;
lean_object* v___y_525_ = stack[9].m_obj;
lean_object* v_res_538_;
v_res_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_516_, v___x_517_, v_as_518_, v_sz_519_, v_i_520_, v_b_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_538_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4___boxed(lean_object* v___x_539_, lean_object* v___x_540_, lean_object* v_as_541_, lean_object* v_sz_542_, lean_object* v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
size_t v_sz_boxed_550_; size_t v_i_boxed_551_; lean_object* v_res_552_; 
v_sz_boxed_550_ = lean_unbox_usize(v_sz_542_);
lean_dec(v_sz_542_);
v_i_boxed_551_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_539_, v___x_540_, v_as_541_, v_sz_boxed_550_, v_i_boxed_551_, v_b_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec_ref(v_as_541_);
return v_res_552_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(lean_object* v___x_553_, uint8_t v___x_554_, lean_object* v_targs_555_, lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; 
v___x_562_ = l_Lean_Expr_sort___override(v___x_553_);
v___x_563_ = 0;
v___x_564_ = 1;
v___x_565_ = l_Lean_Meta_mkLambdaFVars(v_targs_555_, v___x_562_, v___x_563_, v___x_554_, v___x_563_, v___x_554_, v___x_564_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
return v___x_565_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_553_ = stack[0].m_obj;
uint8_t v___x_554_ = stack[1].m_num;
lean_object* v_targs_555_ = stack[2].m_obj;
lean_object* v_x_556_ = stack[3].m_obj;
lean_object* v___y_557_ = stack[4].m_obj;
lean_object* v___y_558_ = stack[5].m_obj;
lean_object* v___y_559_ = stack[6].m_obj;
lean_object* v___y_560_ = stack[7].m_obj;
lean_object* v_res_566_;
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_553_, v___x_554_, v_targs_555_, v_x_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed(lean_object* v___x_567_, lean_object* v___x_568_, lean_object* v_targs_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_9204__boxed_576_; lean_object* v_res_577_; 
v___x_9204__boxed_576_ = lean_unbox(v___x_568_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_567_, v___x_9204__boxed_576_, v_targs_569_, v_x_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_x_570_);
lean_dec_ref(v_targs_569_);
return v_res_577_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object* v___x_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v_as_581_, size_t v_sz_582_, size_t v_i_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_lt(v_i_583_, v_sz_582_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_dec(v___x_578_);
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_b_584_);
return v___x_591_;
}
else
{
uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___f_594_; lean_object* v_a_595_; lean_object* v___x_596_; 
v___x_592_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
v___x_593_ = lean_box(v___x_592_);
lean_inc(v___x_578_);
v___f_594_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_594_, 0, v___x_578_);
lean_closure_set(v___f_594_, 1, v___x_593_);
v_a_595_ = lean_array_uget_borrowed(v_as_581_, v_i_583_);
lean_inc(v___y_588_);
lean_inc_ref(v___y_587_);
lean_inc(v___y_586_);
lean_inc_ref(v___y_585_);
lean_inc(v_a_595_);
v___x_596_ = lean_infer_type(v_a_595_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; lean_object* v___x_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = 0;
v___x_599_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_597_, v___f_594_, v___x_598_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; size_t v___x_602_; size_t v___x_603_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = l_Lean_Expr_app___override(v_b_584_, v_a_600_);
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_583_, v___x_602_);
v_i_583_ = v___x_603_;
v_b_584_ = v___x_601_;
goto _start;
}
else
{
lean_dec_ref(v_b_584_);
lean_dec(v___x_578_);
return v___x_599_;
}
}
else
{
lean_dec_ref(v___f_594_);
lean_dec_ref(v_b_584_);
lean_dec(v___x_578_);
return v___x_596_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_578_ = stack[0].m_obj;
lean_object* v___x_579_ = stack[1].m_obj;
lean_object* v___x_580_ = stack[2].m_obj;
lean_object* v_as_581_ = stack[3].m_obj;
size_t v_sz_582_ = stack[4].m_num;
size_t v_i_583_ = stack[5].m_num;
lean_object* v_b_584_ = stack[6].m_obj;
lean_object* v___y_585_ = stack[7].m_obj;
lean_object* v___y_586_ = stack[8].m_obj;
lean_object* v___y_587_ = stack[9].m_obj;
lean_object* v___y_588_ = stack[10].m_obj;
lean_object* v_res_605_;
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_578_, v___x_579_, v___x_580_, v_as_581_, v_sz_582_, v_i_583_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object* v___x_606_, lean_object* v___x_607_, lean_object* v___x_608_, lean_object* v_as_609_, lean_object* v_sz_610_, lean_object* v_i_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
size_t v_sz_boxed_618_; size_t v_i_boxed_619_; lean_object* v_res_620_; 
v_sz_boxed_618_ = lean_unbox_usize(v_sz_610_);
lean_dec(v_sz_610_);
v_i_boxed_619_ = lean_unbox_usize(v_i_611_);
lean_dec(v_i_611_);
v_res_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_606_, v___x_607_, v___x_608_, v_as_609_, v_sz_boxed_618_, v_i_boxed_619_, v_b_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec_ref(v_as_609_);
lean_dec(v___x_608_);
lean_dec(v___x_607_);
return v_res_620_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(lean_object* v_msgData_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; lean_object* v_env_628_; uint8_t v___x_629_; lean_object* v_env_630_; lean_object* v___x_631_; lean_object* v_toCold_632_; lean_object* v_mctx_633_; lean_object* v_lctx_634_; lean_object* v_options_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_627_ = lean_st_ref_get(v___y_625_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_628_);
lean_dec(v___x_627_);
v___x_629_ = 0;
v_env_630_ = l_Lean_Environment_setRecordingDeps(v_env_628_, v___x_629_);
v___x_631_ = lean_st_ref_get(v___y_623_);
v_toCold_632_ = lean_ctor_get(v___y_624_, 0);
v_mctx_633_ = lean_ctor_get(v___x_631_, 0);
lean_inc_ref(v_mctx_633_);
lean_dec(v___x_631_);
v_lctx_634_ = lean_ctor_get(v___y_622_, 2);
v_options_635_ = lean_ctor_get(v_toCold_632_, 2);
lean_inc_ref(v_options_635_);
lean_inc_ref(v_lctx_634_);
v___x_636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_636_, 0, v_env_630_);
lean_ctor_set(v___x_636_, 1, v_mctx_633_);
lean_ctor_set(v___x_636_, 2, v_lctx_634_);
lean_ctor_set(v___x_636_, 3, v_options_635_);
v___x_637_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_msgData_621_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_621_ = stack[0].m_obj;
lean_object* v___y_622_ = stack[1].m_obj;
lean_object* v___y_623_ = stack[2].m_obj;
lean_object* v___y_624_ = stack[3].m_obj;
lean_object* v___y_625_ = stack[4].m_obj;
lean_object* v_res_639_;
v_res_639_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_663_; 
v_ref_653_ = lean_ctor_get(v___y_650_, 2);
v___x_654_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_663_ == 0)
{
v___x_657_ = v___x_654_;
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_663_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_inc(v_ref_653_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_ref_653_);
lean_ctor_set(v___x_659_, 1, v_a_655_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 1);
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_647_ = stack[0].m_obj;
lean_object* v___y_648_ = stack[1].m_obj;
lean_object* v___y_649_ = stack[2].m_obj;
lean_object* v___y_650_ = stack[3].m_obj;
lean_object* v___y_651_ = stack[4].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_676_ = lean_unsigned_to_nat(4u);
v___x_677_ = lean_unsigned_to_nat(68u);
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_680_ = l_mkPanicMessageWithDecl(v___x_679_, v___x_678_, v___x_677_, v___x_676_, v___x_675_);
return v___x_680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_687_, lean_object* v_numMotives_688_, lean_object* v_numMinors_689_, lean_object* v___x_690_, lean_object* v_head_691_, lean_object* v_tail_692_, lean_object* v_recName_693_, lean_object* v_belowName_694_, lean_object* v_levelParams_695_, lean_object* v_refArgs_696_, lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_703_ = lean_nat_add(v_nParams_687_, v_numMotives_688_);
v___x_704_ = lean_nat_add(v___x_703_, v_numMinors_689_);
v___x_705_ = lean_array_get_size(v_refArgs_696_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v___x_704_);
lean_dec(v___x_703_);
lean_dec_ref(v_refArgs_696_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
lean_dec(v_recName_693_);
lean_dec(v_tail_692_);
lean_dec(v_head_691_);
lean_dec(v_nParams_687_);
v___x_707_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_708_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_707_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_708_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_709_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_687_);
lean_inc_ref_n(v_refArgs_696_, 4);
v___x_710_ = l_Array_toSubarray___redArg(v_refArgs_696_, v___x_709_, v_nParams_687_);
v___x_711_ = l_Subarray_copy___redArg(v___x_710_);
lean_inc(v___x_703_);
v___x_712_ = l_Array_toSubarray___redArg(v_refArgs_696_, v_nParams_687_, v___x_703_);
v___x_713_ = l_Subarray_copy___redArg(v___x_712_);
lean_inc_n(v___x_704_, 2);
v___x_714_ = l_Array_toSubarray___redArg(v_refArgs_696_, v___x_703_, v___x_704_);
v___x_715_ = l_Subarray_copy___redArg(v___x_714_);
v___x_716_ = lean_unsigned_to_nat(1u);
v___x_717_ = lean_nat_sub(v___x_705_, v___x_716_);
lean_inc(v___x_717_);
v___x_718_ = l_Array_toSubarray___redArg(v_refArgs_696_, v___x_704_, v___x_717_);
v___x_719_ = l_Subarray_copy___redArg(v___x_718_);
v___x_720_ = lean_array_get(v___x_690_, v_refArgs_696_, v___x_717_);
lean_dec(v___x_717_);
lean_dec_ref(v_refArgs_696_);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc(v___x_720_);
v___x_721_ = lean_infer_type(v___x_720_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
v___x_723_ = lean_infer_type(v_a_722_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_Meta_typeFormerTypeLevel(v_a_724_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
if (lean_obj_tag(v_a_726_) == 1)
{
lean_object* v_val_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; size_t v_sz_733_; size_t v___x_734_; lean_object* v___x_735_; 
v_val_727_ = lean_ctor_get(v_a_726_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v_a_726_, 1);
v___x_728_ = l_Lean_mkLevelMax(v_val_727_, v_head_691_);
lean_inc_n(v___x_728_, 2);
v___x_729_ = l_Lean_Level_succ___override(v___x_728_);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_tail_692_);
v___x_731_ = l_Lean_Expr_const___override(v_recName_693_, v___x_730_);
v___x_732_ = l_Lean_mkAppN(v___x_731_, v___x_711_);
v_sz_733_ = lean_array_size(v___x_713_);
v___x_734_ = ((size_t)0ULL);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_728_, v___x_704_, v___x_705_, v___x_713_, v_sz_733_, v___x_734_, v___x_732_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___x_704_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; size_t v_sz_737_; lean_object* v___x_738_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v_sz_737_ = lean_array_size(v___x_715_);
lean_inc_ref(v___x_713_);
lean_inc(v___x_728_);
v___x_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_728_, v___x_713_, v___x_715_, v_sz_737_, v___x_734_, v_a_736_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec_ref(v___x_715_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = l_Lean_mkAppN(v_a_739_, v___x_719_);
lean_inc(v___x_720_);
v___x_741_ = l_Lean_Expr_app___override(v___x_740_, v___x_720_);
v___x_742_ = l_Array_append___redArg(v___x_711_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_743_ = l_Array_append___redArg(v___x_742_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_744_ = lean_mk_empty_array_with_capacity(v___x_716_);
v___x_745_ = lean_array_push(v___x_744_, v___x_720_);
v___x_746_ = l_Array_append___redArg(v___x_743_, v___x_745_);
lean_dec_ref(v___x_745_);
v___x_747_ = l_Lean_Expr_sort___override(v___x_728_);
v___x_748_ = 0;
v___x_749_ = 1;
v___x_750_ = l_Lean_Meta_mkForallFVars(v___x_746_, v___x_747_, v___x_748_, v___x_706_, v___x_706_, v___x_749_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = l_Lean_Meta_mkLambdaFVars(v___x_746_, v___x_741_, v___x_748_, v___x_706_, v___x_748_, v___x_706_, v___x_749_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec_ref(v___x_746_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_box(1);
v___x_755_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_694_, v_levelParams_695_, v_a_751_, v_a_753_, v___x_754_, v___y_701_);
return v___x_755_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_a_751_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
v_a_756_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_752_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_752_);
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
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_741_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
v_a_764_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_750_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_750_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v___x_728_);
lean_dec(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
v_a_772_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_738_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_738_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v___x_728_);
lean_dec(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
v_a_780_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_735_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_735_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec(v_a_726_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_704_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
lean_dec(v_recName_693_);
lean_dec(v_tail_692_);
lean_dec(v_head_691_);
v___x_788_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_789_ = l_Lean_MessageData_ofExpr(v___x_720_);
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_792_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
return v___x_793_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_704_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
lean_dec(v_recName_693_);
lean_dec(v_tail_692_);
lean_dec(v_head_691_);
v_a_794_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_725_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_725_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_704_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
lean_dec(v_recName_693_);
lean_dec(v_tail_692_);
lean_dec(v_head_691_);
v_a_802_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_723_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_723_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v___x_720_);
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_704_);
lean_dec(v_levelParams_695_);
lean_dec(v_belowName_694_);
lean_dec(v_recName_693_);
lean_dec(v_tail_692_);
lean_dec(v_head_691_);
v_a_810_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_721_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_721_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_nParams_687_ = stack[0].m_obj;
lean_object* v_numMotives_688_ = stack[1].m_obj;
lean_object* v_numMinors_689_ = stack[2].m_obj;
lean_object* v___x_690_ = stack[3].m_obj;
lean_object* v_head_691_ = stack[4].m_obj;
lean_object* v_tail_692_ = stack[5].m_obj;
lean_object* v_recName_693_ = stack[6].m_obj;
lean_object* v_belowName_694_ = stack[7].m_obj;
lean_object* v_levelParams_695_ = stack[8].m_obj;
lean_object* v_refArgs_696_ = stack[9].m_obj;
lean_object* v_x_697_ = stack[10].m_obj;
lean_object* v___y_698_ = stack[11].m_obj;
lean_object* v___y_699_ = stack[12].m_obj;
lean_object* v___y_700_ = stack[13].m_obj;
lean_object* v___y_701_ = stack[14].m_obj;
lean_object* v_res_818_;
v_res_818_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_687_, v_numMotives_688_, v_numMinors_689_, v___x_690_, v_head_691_, v_tail_692_, v_recName_693_, v_belowName_694_, v_levelParams_695_, v_refArgs_696_, v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_819_, lean_object* v_numMotives_820_, lean_object* v_numMinors_821_, lean_object* v___x_822_, lean_object* v_head_823_, lean_object* v_tail_824_, lean_object* v_recName_825_, lean_object* v_belowName_826_, lean_object* v_levelParams_827_, lean_object* v_refArgs_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_819_, v_numMotives_820_, v_numMinors_821_, v___x_822_, v_head_823_, v_tail_824_, v_recName_825_, v_belowName_826_, v_levelParams_827_, v_refArgs_828_, v_x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_x_829_);
lean_dec_ref(v___x_822_);
lean_dec(v_numMinors_821_);
lean_dec(v_numMotives_820_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
if (lean_obj_tag(v_a_836_) == 0)
{
lean_object* v___x_838_; 
v___x_838_ = l_List_reverse___redArg(v_a_837_);
return v___x_838_;
}
else
{
lean_object* v_head_839_; lean_object* v_tail_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_849_; 
v_head_839_ = lean_ctor_get(v_a_836_, 0);
v_tail_840_ = lean_ctor_get(v_a_836_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_836_);
if (v_isSharedCheck_849_ == 0)
{
v___x_842_ = v_a_836_;
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_tail_840_);
lean_inc(v_head_839_);
lean_dec(v_a_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_849_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_Level_param___override(v_head_839_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v_a_837_);
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_837_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v_a_836_ = v_tail_840_;
v_a_837_ = v___x_846_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_850_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_856_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set(v___x_856_, 2, v___x_855_);
lean_ctor_set(v___x_856_, 3, v___x_855_);
lean_ctor_set(v___x_856_, 4, v___x_855_);
lean_ctor_set(v___x_856_, 5, v___x_855_);
return v___x_856_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_857_, uint8_t v_s_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v_env_863_; lean_object* v_nextMacroScope_864_; lean_object* v_ngen_865_; lean_object* v_auxDeclNGen_866_; lean_object* v_traceState_867_; lean_object* v_recordedDeps_868_; lean_object* v_messages_869_; lean_object* v_infoState_870_; lean_object* v_snapshotTasks_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_900_; 
v___x_862_ = lean_st_ref_take(v___y_860_);
v_env_863_ = lean_ctor_get(v___x_862_, 0);
v_nextMacroScope_864_ = lean_ctor_get(v___x_862_, 1);
v_ngen_865_ = lean_ctor_get(v___x_862_, 2);
v_auxDeclNGen_866_ = lean_ctor_get(v___x_862_, 3);
v_traceState_867_ = lean_ctor_get(v___x_862_, 4);
v_recordedDeps_868_ = lean_ctor_get(v___x_862_, 6);
v_messages_869_ = lean_ctor_get(v___x_862_, 7);
v_infoState_870_ = lean_ctor_get(v___x_862_, 8);
v_snapshotTasks_871_ = lean_ctor_get(v___x_862_, 9);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v___x_862_, 5);
lean_dec(v_unused_901_);
v___x_873_ = v___x_862_;
v_isShared_874_ = v_isSharedCheck_900_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snapshotTasks_871_);
lean_inc(v_infoState_870_);
lean_inc(v_messages_869_);
lean_inc(v_recordedDeps_868_);
lean_inc(v_traceState_867_);
lean_inc(v_auxDeclNGen_866_);
lean_inc(v_ngen_865_);
lean_inc(v_nextMacroScope_864_);
lean_inc(v_env_863_);
lean_dec(v___x_862_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_900_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_875_ = 0;
v___x_876_ = lean_box(0);
v___x_877_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_863_, v_declName_857_, v_s_858_, v___x_875_, v___x_876_);
v___x_878_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 5, v___x_878_);
lean_ctor_set(v___x_873_, 0, v___x_877_);
v___x_880_ = v___x_873_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v_nextMacroScope_864_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_ngen_865_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_auxDeclNGen_866_);
lean_ctor_set(v_reuseFailAlloc_899_, 4, v_traceState_867_);
lean_ctor_set(v_reuseFailAlloc_899_, 5, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_899_, 6, v_recordedDeps_868_);
lean_ctor_set(v_reuseFailAlloc_899_, 7, v_messages_869_);
lean_ctor_set(v_reuseFailAlloc_899_, 8, v_infoState_870_);
lean_ctor_set(v_reuseFailAlloc_899_, 9, v_snapshotTasks_871_);
v___x_880_ = v_reuseFailAlloc_899_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v_mctx_883_; lean_object* v_zetaDeltaFVarIds_884_; lean_object* v_postponed_885_; lean_object* v_diag_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_897_; 
v___x_881_ = lean_st_ref_put(v___y_860_, v___x_880_);
v___x_882_ = lean_st_ref_take(v___y_859_);
v_mctx_883_ = lean_ctor_get(v___x_882_, 0);
v_zetaDeltaFVarIds_884_ = lean_ctor_get(v___x_882_, 2);
v_postponed_885_ = lean_ctor_get(v___x_882_, 3);
v_diag_886_ = lean_ctor_get(v___x_882_, 4);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_882_, 1);
lean_dec(v_unused_898_);
v___x_888_ = v___x_882_;
v_isShared_889_ = v_isSharedCheck_897_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_diag_886_);
lean_inc(v_postponed_885_);
lean_inc(v_zetaDeltaFVarIds_884_);
lean_inc(v_mctx_883_);
lean_dec(v___x_882_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_897_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_891_);
v___x_893_ = v___x_888_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_mctx_883_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v_zetaDeltaFVarIds_884_);
lean_ctor_set(v_reuseFailAlloc_896_, 3, v_postponed_885_);
lean_ctor_set(v_reuseFailAlloc_896_, 4, v_diag_886_);
v___x_893_ = v_reuseFailAlloc_896_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_st_ref_put(v___y_859_, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_890_);
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_857_ = stack[0].m_obj;
uint8_t v_s_858_ = stack[1].m_num;
lean_object* v___y_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v_res_902_;
v_res_902_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_857_, v_s_858_, v___y_859_, v___y_860_);
stack->m_obj
 = v_res_902_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_903_, lean_object* v_s_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
uint8_t v_s_boxed_908_; lean_object* v_res_909_; 
v_s_boxed_908_ = lean_unbox(v_s_904_);
v_res_909_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_903_, v_s_boxed_908_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
return v_res_909_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
uint8_t v___x_916_; lean_object* v___x_917_; 
v___x_916_ = 0;
v___x_917_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_910_, v___x_916_, v___y_912_, v___y_914_);
return v___x_917_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_910_ = stack[0].m_obj;
lean_object* v___y_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v___y_913_ = stack[3].m_obj;
lean_object* v___y_914_ = stack[4].m_obj;
lean_object* v_res_918_;
v_res_918_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
stack->m_obj
 = v_res_918_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_926_, lean_object* v_msg_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_toCold_933_; lean_object* v_currRecDepth_934_; lean_object* v_ref_935_; uint16_t v_optionFlags_936_; uint8_t v_suppressElabErrors_937_; uint8_t v_isRecordingDeps_938_; lean_object* v_ref_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v_toCold_933_ = lean_ctor_get(v___y_930_, 0);
v_currRecDepth_934_ = lean_ctor_get(v___y_930_, 1);
v_ref_935_ = lean_ctor_get(v___y_930_, 2);
v_optionFlags_936_ = lean_ctor_get_uint16(v___y_930_, sizeof(void*)*3);
v_suppressElabErrors_937_ = lean_ctor_get_uint8(v___y_930_, sizeof(void*)*3 + 2);
v_isRecordingDeps_938_ = lean_ctor_get_uint8(v___y_930_, sizeof(void*)*3 + 3);
v_ref_939_ = l_Lean_replaceRef(v_ref_926_, v_ref_935_);
lean_inc(v_currRecDepth_934_);
lean_inc_ref(v_toCold_933_);
v___x_940_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_940_, 0, v_toCold_933_);
lean_ctor_set(v___x_940_, 1, v_currRecDepth_934_);
lean_ctor_set(v___x_940_, 2, v_ref_939_);
lean_ctor_set_uint16(v___x_940_, sizeof(void*)*3, v_optionFlags_936_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 2, v_suppressElabErrors_937_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*3 + 3, v_isRecordingDeps_938_);
v___x_941_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_927_, v___y_928_, v___y_929_, v___x_940_, v___y_931_);
lean_dec_ref_known(v___x_940_, 3);
return v___x_941_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_926_ = stack[0].m_obj;
lean_object* v_msg_927_ = stack[1].m_obj;
lean_object* v___y_928_ = stack[2].m_obj;
lean_object* v___y_929_ = stack[3].m_obj;
lean_object* v___y_930_ = stack[4].m_obj;
lean_object* v___y_931_ = stack[5].m_obj;
lean_object* v_res_942_;
v_res_942_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_926_, v_msg_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
stack->m_obj
 = v_res_942_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_943_, lean_object* v_msg_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_943_, v_msg_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v_ref_943_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_953_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v___x_955_);
lean_ctor_set(v___x_956_, 4, v___x_954_);
lean_ctor_set(v___x_956_, 5, v___x_954_);
lean_ctor_set(v___x_956_, 6, v___x_954_);
lean_ctor_set(v___x_956_, 7, v___x_954_);
lean_ctor_set(v___x_956_, 8, v___x_954_);
lean_ctor_set(v___x_956_, 9, v___x_954_);
lean_ctor_set(v___x_956_, 10, v___x_954_);
lean_ctor_set(v___x_956_, 11, v___x_953_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_unsigned_to_nat(32u);
v___x_958_ = lean_mk_empty_array_with_capacity(v___x_957_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_960_ = ((size_t)5ULL);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_unsigned_to_nat(32u);
v___x_963_ = lean_mk_empty_array_with_capacity(v___x_962_);
v___x_964_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_965_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_963_);
lean_ctor_set(v___x_965_, 2, v___x_961_);
lean_ctor_set(v___x_965_, 3, v___x_961_);
lean_ctor_set_usize(v___x_965_, 4, v___x_960_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_966_ = lean_box(1);
v___x_967_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_966_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_972_ = l_Lean_stringToMessageData(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_984_ = l_Lean_stringToMessageData(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_987_ = l_Lean_stringToMessageData(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__21));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__23));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__25));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_1003_, lean_object* v_declHint_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_env_1009_; uint8_t v___x_1010_; 
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_st_ref_get(v___y_1005_);
v_env_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_env_1009_);
lean_dec(v___x_1008_);
v___x_1010_ = l_Lean_Name_isAnonymous(v_declHint_1004_);
if (v___x_1010_ == 0)
{
uint8_t v_isExporting_1011_; 
v_isExporting_1011_ = lean_ctor_get_uint8(v_env_1009_, sizeof(void*)*13);
if (v_isExporting_1011_ == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_msg_1003_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_inc_ref(v_env_1009_);
v___x_1013_ = l_Lean_Environment_setExporting(v_env_1009_, v___x_1010_);
lean_inc(v_declHint_1004_);
lean_inc_ref(v___x_1013_);
v___x_1014_ = l_Lean_Environment_contains(v___x_1013_, v_declHint_1004_, v_isExporting_1011_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_msg_1003_);
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_c_1021_; lean_object* v___x_1022_; 
v___x_1016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_1018_ = l_Lean_Options_empty;
v___x_1019_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1016_);
lean_ctor_set(v___x_1019_, 2, v___x_1017_);
lean_ctor_set(v___x_1019_, 3, v___x_1018_);
lean_inc(v_declHint_1004_);
v___x_1020_ = l_Lean_MessageData_ofConstName(v_declHint_1004_, v___x_1010_);
v_c_1021_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1021_, 0, v___x_1019_);
lean_ctor_set(v_c_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1009_, v_declHint_1004_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_c_1021_);
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_MessageData_note(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_msg_1003_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
else
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1086_; 
v_val_1030_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1032_ = v___x_1022_;
v_isShared_1033_ = v_isSharedCheck_1086_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v___x_1022_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1086_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v_modules_1035_; lean_object* v_moduleNames_1036_; lean_object* v_mod_1037_; uint8_t v___y_1039_; uint8_t v___x_1069_; 
v___x_1034_ = l_Lean_Environment_header(v_env_1009_);
lean_dec_ref(v_env_1009_);
v_modules_1035_ = lean_ctor_get(v___x_1034_, 3);
lean_inc_ref(v_modules_1035_);
v_moduleNames_1036_ = lean_ctor_get(v___x_1034_, 4);
lean_inc_ref(v_moduleNames_1036_);
lean_dec_ref(v___x_1034_);
v_mod_1037_ = lean_array_get(v___x_1007_, v_moduleNames_1036_, v_val_1030_);
lean_dec_ref(v_moduleNames_1036_);
v___x_1069_ = l_Lean_isPrivateName(v_declHint_1004_);
lean_dec(v_declHint_1004_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = lean_array_get_size(v_modules_1035_);
v___x_1071_ = lean_nat_dec_lt(v_val_1030_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v_modules_1035_);
lean_dec(v_val_1030_);
v___y_1039_ = v___x_1069_;
goto v___jp_1038_;
}
else
{
lean_object* v___x_1072_; lean_object* v_toImport_1073_; uint8_t v_isExported_1074_; 
v___x_1072_ = lean_array_fget(v_modules_1035_, v_val_1030_);
lean_dec(v_val_1030_);
lean_dec_ref(v_modules_1035_);
v_toImport_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref(v_toImport_1073_);
lean_dec(v___x_1072_);
v_isExported_1074_ = lean_ctor_get_uint8(v_toImport_1073_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1073_);
v___y_1039_ = v_isExported_1074_;
goto v___jp_1038_;
}
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec_ref(v_modules_1035_);
lean_del_object(v___x_1032_);
lean_dec(v_val_1030_);
v___x_1075_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_c_1021_);
v___x_1077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__24);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_MessageData_ofName(v_mod_1037_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__26);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_MessageData_note(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_msg_1003_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
v___jp_1038_:
{
if (v___y_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1040_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_c_1021_);
v___x_1042_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = l_Lean_MessageData_ofName(v_mod_1037_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_note(v___x_1047_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_msg_1003_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1049_);
v___x_1051_ = v___x_1032_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_c_1021_);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_ofName(v_mod_1037_);
lean_inc_ref(v___x_1057_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__20);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1057_);
v___x_1062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__22);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = l_Lean_MessageData_note(v___x_1063_);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v_msg_1003_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1065_);
v___x_1067_ = v___x_1032_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
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
lean_object* v___x_1087_; 
lean_dec_ref(v_env_1009_);
lean_dec(v_declHint_1004_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_msg_1003_);
return v___x_1087_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1003_ = stack[0].m_obj;
lean_object* v_declHint_1004_ = stack[1].m_obj;
lean_object* v___y_1005_ = stack[2].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1003_, v_declHint_1004_, v___y_1005_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1089_, lean_object* v_declHint_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1089_, v_declHint_1090_, v___y_1091_);
lean_dec(v___y_1091_);
return v_res_1093_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1094_, lean_object* v_declHint_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1111_; 
v___x_1101_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1094_, v_declHint_1095_, v___y_1099_);
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1106_ = l_Lean_unknownIdentifierMessageTag;
v___x_1107_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_a_1102_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1094_ = stack[0].m_obj;
lean_object* v_declHint_1095_ = stack[1].m_obj;
lean_object* v___y_1096_ = stack[2].m_obj;
lean_object* v___y_1097_ = stack[3].m_obj;
lean_object* v___y_1098_ = stack[4].m_obj;
lean_object* v___y_1099_ = stack[5].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1094_, v_declHint_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1113_, lean_object* v_declHint_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1113_, v_declHint_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1121_, lean_object* v_msg_1122_, lean_object* v_declHint_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; 
v___x_1129_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1122_, v_declHint_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1121_, v_a_1130_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1131_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1121_ = stack[0].m_obj;
lean_object* v_msg_1122_ = stack[1].m_obj;
lean_object* v_declHint_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v___y_1125_ = stack[4].m_obj;
lean_object* v___y_1126_ = stack[5].m_obj;
lean_object* v___y_1127_ = stack[6].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1121_, v_msg_1122_, v_declHint_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1133_, lean_object* v_msg_1134_, lean_object* v_declHint_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1133_, v_msg_1134_, v_declHint_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v_ref_1133_);
return v_res_1141_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1148_, lean_object* v_constName_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1155_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1156_ = 0;
lean_inc(v_constName_1149_);
v___x_1157_ = l_Lean_MessageData_ofConstName(v_constName_1149_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1158_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
v___x_1161_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1148_, v___x_1160_, v_constName_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1161_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1148_ = stack[0].m_obj;
lean_object* v_constName_1149_ = stack[1].m_obj;
lean_object* v___y_1150_ = stack[2].m_obj;
lean_object* v___y_1151_ = stack[3].m_obj;
lean_object* v___y_1152_ = stack[4].m_obj;
lean_object* v___y_1153_ = stack[5].m_obj;
lean_object* v_res_1162_;
v_res_1162_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1148_, v_constName_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
stack->m_obj
 = v_res_1162_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1163_, lean_object* v_constName_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1163_, v_constName_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v_ref_1163_);
return v_res_1170_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_ref_1177_; lean_object* v___x_1178_; 
v_ref_1177_ = lean_ctor_get(v___y_1174_, 2);
v___x_1178_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1177_, v_constName_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1178_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1171_ = stack[0].m_obj;
lean_object* v___y_1172_ = stack[1].m_obj;
lean_object* v___y_1173_ = stack[2].m_obj;
lean_object* v___y_1174_ = stack[3].m_obj;
lean_object* v___y_1175_ = stack[4].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; lean_object* v_env_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = lean_st_ref_get(v___y_1191_);
v_env_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_ref(v_env_1194_);
lean_dec(v___x_1193_);
v___x_1195_ = 0;
lean_inc(v_constName_1187_);
v___x_1196_ = l_Lean_Environment_find_x3f(v_env_1194_, v_constName_1187_, v___x_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v_constName_1187_);
v_val_1198_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 0);
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_val_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1187_ = stack[0].m_obj;
lean_object* v___y_1188_ = stack[1].m_obj;
lean_object* v___y_1189_ = stack[2].m_obj;
lean_object* v___y_1190_ = stack[3].m_obj;
lean_object* v___y_1191_ = stack[4].m_obj;
lean_object* v_res_1206_;
v_res_1206_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1216_ = l_Lean_stringToMessageData(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1223_, lean_object* v_nParams_1224_, lean_object* v_belowName_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1223_);
v___x_1232_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1223_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
if (lean_obj_tag(v_a_1233_) == 7)
{
lean_object* v_val_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1351_; 
v_val_1234_ = lean_ctor_get(v_a_1233_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1233_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1236_ = v_a_1233_;
v_isShared_1237_ = v_isSharedCheck_1351_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_val_1234_);
lean_dec(v_a_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1351_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_toConstantVal_1238_; lean_object* v_numMotives_1239_; lean_object* v_numMinors_1240_; lean_object* v_levelParams_1241_; lean_object* v_type_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_toConstantVal_1238_ = lean_ctor_get(v_val_1234_, 0);
lean_inc_ref(v_toConstantVal_1238_);
v_numMotives_1239_ = lean_ctor_get(v_val_1234_, 4);
lean_inc(v_numMotives_1239_);
v_numMinors_1240_ = lean_ctor_get(v_val_1234_, 5);
lean_inc(v_numMinors_1240_);
lean_dec_ref(v_val_1234_);
v_levelParams_1241_ = lean_ctor_get(v_toConstantVal_1238_, 1);
lean_inc_n(v_levelParams_1241_, 2);
v_type_1242_ = lean_ctor_get(v_toConstantVal_1238_, 2);
lean_inc_ref(v_type_1242_);
lean_dec_ref(v_toConstantVal_1238_);
v___x_1243_ = lean_box(0);
v___x_1244_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1241_, v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_head_1245_; lean_object* v_tail_1246_; lean_object* v___f_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v_head_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_head_1245_);
v_tail_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_tail_1246_);
lean_dec_ref_known(v___x_1244_, 2);
v___f_1247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1247_, 0, v_nParams_1224_);
lean_closure_set(v___f_1247_, 1, v_numMotives_1239_);
lean_closure_set(v___f_1247_, 2, v_numMinors_1240_);
lean_closure_set(v___f_1247_, 3, v___x_1231_);
lean_closure_set(v___f_1247_, 4, v_head_1245_);
lean_closure_set(v___f_1247_, 5, v_tail_1246_);
lean_closure_set(v___f_1247_, 6, v_recName_1223_);
lean_closure_set(v___f_1247_, 7, v_belowName_1225_);
lean_closure_set(v___f_1247_, 8, v_levelParams_1241_);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1242_, v___f_1247_, v___x_1248_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1252_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc_n(v_a_1250_, 2);
lean_dec_ref_known(v___x_1249_, 1);
if (v_isShared_1237_ == 0)
{
lean_ctor_set_tag(v___x_1236_, 1);
lean_ctor_set(v___x_1236_, 0, v_a_1250_);
v___x_1252_ = v___x_1236_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1250_);
v___x_1252_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_addDecl(v___x_1252_, v___x_1248_, v_a_1228_, v_a_1229_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_toConstantVal_1254_; lean_object* v_name_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref_known(v___x_1253_, 1);
v_toConstantVal_1254_ = lean_ctor_get(v_a_1250_, 0);
lean_inc_ref(v_toConstantVal_1254_);
lean_dec(v_a_1250_);
v_name_1255_ = lean_ctor_get(v_toConstantVal_1254_, 0);
lean_inc_n(v_name_1255_, 2);
lean_dec_ref(v_toConstantVal_1254_);
v___x_1256_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1255_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1335_);
v___x_1258_ = v___x_1256_;
v_isShared_1259_ = v_isSharedCheck_1334_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1256_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1334_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v_env_1261_; lean_object* v_nextMacroScope_1262_; lean_object* v_ngen_1263_; lean_object* v_auxDeclNGen_1264_; lean_object* v_traceState_1265_; lean_object* v_recordedDeps_1266_; lean_object* v_messages_1267_; lean_object* v_infoState_1268_; lean_object* v_snapshotTasks_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1332_; 
v___x_1260_ = lean_st_ref_take(v_a_1229_);
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
v_nextMacroScope_1262_ = lean_ctor_get(v___x_1260_, 1);
v_ngen_1263_ = lean_ctor_get(v___x_1260_, 2);
v_auxDeclNGen_1264_ = lean_ctor_get(v___x_1260_, 3);
v_traceState_1265_ = lean_ctor_get(v___x_1260_, 4);
v_recordedDeps_1266_ = lean_ctor_get(v___x_1260_, 6);
v_messages_1267_ = lean_ctor_get(v___x_1260_, 7);
v_infoState_1268_ = lean_ctor_get(v___x_1260_, 8);
v_snapshotTasks_1269_ = lean_ctor_get(v___x_1260_, 9);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1260_, 5);
lean_dec(v_unused_1333_);
v___x_1271_ = v___x_1260_;
v_isShared_1272_ = v_isSharedCheck_1332_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snapshotTasks_1269_);
lean_inc(v_infoState_1268_);
lean_inc(v_messages_1267_);
lean_inc(v_recordedDeps_1266_);
lean_inc(v_traceState_1265_);
lean_inc(v_auxDeclNGen_1264_);
lean_inc(v_ngen_1263_);
lean_inc(v_nextMacroScope_1262_);
lean_inc(v_env_1261_);
lean_dec(v___x_1260_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1332_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_inc(v_name_1255_);
v___x_1273_ = l_Lean_markAuxRecursor(v_env_1261_, v_name_1255_);
v___x_1274_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 5, v___x_1274_);
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_nextMacroScope_1262_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_ngen_1263_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_auxDeclNGen_1264_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_traceState_1265_);
lean_ctor_set(v_reuseFailAlloc_1331_, 5, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1331_, 6, v_recordedDeps_1266_);
lean_ctor_set(v_reuseFailAlloc_1331_, 7, v_messages_1267_);
lean_ctor_set(v_reuseFailAlloc_1331_, 8, v_infoState_1268_);
lean_ctor_set(v_reuseFailAlloc_1331_, 9, v_snapshotTasks_1269_);
v___x_1276_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_mctx_1279_; lean_object* v_zetaDeltaFVarIds_1280_; lean_object* v_postponed_1281_; lean_object* v_diag_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1329_; 
v___x_1277_ = lean_st_ref_put(v_a_1229_, v___x_1276_);
v___x_1278_ = lean_st_ref_take(v_a_1227_);
v_mctx_1279_ = lean_ctor_get(v___x_1278_, 0);
v_zetaDeltaFVarIds_1280_ = lean_ctor_get(v___x_1278_, 2);
v_postponed_1281_ = lean_ctor_get(v___x_1278_, 3);
v_diag_1282_ = lean_ctor_get(v___x_1278_, 4);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1278_, 1);
lean_dec(v_unused_1330_);
v___x_1284_ = v___x_1278_;
v_isShared_1285_ = v_isSharedCheck_1329_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_diag_1282_);
lean_inc(v_postponed_1281_);
lean_inc(v_zetaDeltaFVarIds_1280_);
lean_inc(v_mctx_1279_);
lean_dec(v___x_1278_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1329_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_mctx_1279_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_zetaDeltaFVarIds_1280_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_postponed_1281_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_diag_1282_);
v___x_1288_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_env_1291_; lean_object* v_nextMacroScope_1292_; lean_object* v_ngen_1293_; lean_object* v_auxDeclNGen_1294_; lean_object* v_traceState_1295_; lean_object* v_recordedDeps_1296_; lean_object* v_messages_1297_; lean_object* v_infoState_1298_; lean_object* v_snapshotTasks_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1326_; 
v___x_1289_ = lean_st_ref_put(v_a_1227_, v___x_1288_);
v___x_1290_ = lean_st_ref_take(v_a_1229_);
v_env_1291_ = lean_ctor_get(v___x_1290_, 0);
v_nextMacroScope_1292_ = lean_ctor_get(v___x_1290_, 1);
v_ngen_1293_ = lean_ctor_get(v___x_1290_, 2);
v_auxDeclNGen_1294_ = lean_ctor_get(v___x_1290_, 3);
v_traceState_1295_ = lean_ctor_get(v___x_1290_, 4);
v_recordedDeps_1296_ = lean_ctor_get(v___x_1290_, 6);
v_messages_1297_ = lean_ctor_get(v___x_1290_, 7);
v_infoState_1298_ = lean_ctor_get(v___x_1290_, 8);
v_snapshotTasks_1299_ = lean_ctor_get(v___x_1290_, 9);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1290_, 5);
lean_dec(v_unused_1327_);
v___x_1301_ = v___x_1290_;
v_isShared_1302_ = v_isSharedCheck_1326_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snapshotTasks_1299_);
lean_inc(v_infoState_1298_);
lean_inc(v_messages_1297_);
lean_inc(v_recordedDeps_1296_);
lean_inc(v_traceState_1295_);
lean_inc(v_auxDeclNGen_1294_);
lean_inc(v_ngen_1293_);
lean_inc(v_nextMacroScope_1292_);
lean_inc(v_env_1291_);
lean_dec(v___x_1290_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1326_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = l_Lean_addProtected(v_env_1291_, v_name_1255_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 5, v___x_1274_);
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_nextMacroScope_1292_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_ngen_1293_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_auxDeclNGen_1294_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v_traceState_1295_);
lean_ctor_set(v_reuseFailAlloc_1325_, 5, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1325_, 6, v_recordedDeps_1296_);
lean_ctor_set(v_reuseFailAlloc_1325_, 7, v_messages_1297_);
lean_ctor_set(v_reuseFailAlloc_1325_, 8, v_infoState_1298_);
lean_ctor_set(v_reuseFailAlloc_1325_, 9, v_snapshotTasks_1299_);
v___x_1305_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_mctx_1308_; lean_object* v_zetaDeltaFVarIds_1309_; lean_object* v_postponed_1310_; lean_object* v_diag_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1323_; 
v___x_1306_ = lean_st_ref_put(v_a_1229_, v___x_1305_);
v___x_1307_ = lean_st_ref_take(v_a_1227_);
v_mctx_1308_ = lean_ctor_get(v___x_1307_, 0);
v_zetaDeltaFVarIds_1309_ = lean_ctor_get(v___x_1307_, 2);
v_postponed_1310_ = lean_ctor_get(v___x_1307_, 3);
v_diag_1311_ = lean_ctor_get(v___x_1307_, 4);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1307_, 1);
lean_dec(v_unused_1324_);
v___x_1313_ = v___x_1307_;
v_isShared_1314_ = v_isSharedCheck_1323_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_diag_1311_);
lean_inc(v_postponed_1310_);
lean_inc(v_zetaDeltaFVarIds_1309_);
lean_inc(v_mctx_1308_);
lean_dec(v___x_1307_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1323_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1315_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 1, v___x_1286_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_mctx_1308_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_zetaDeltaFVarIds_1309_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_postponed_1310_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_diag_1311_);
v___x_1317_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_st_ref_put(v_a_1227_, v___x_1317_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v___x_1315_);
v___x_1320_ = v___x_1258_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
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
lean_dec(v_a_1250_);
return v___x_1253_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_del_object(v___x_1236_);
v_a_1337_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1249_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1249_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
lean_dec(v___x_1244_);
lean_dec_ref(v_type_1242_);
lean_dec(v_levelParams_1241_);
lean_dec(v_numMinors_1240_);
lean_dec(v_numMotives_1239_);
lean_del_object(v___x_1236_);
lean_dec(v_belowName_1225_);
lean_dec(v_nParams_1224_);
v___x_1345_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1346_ = l_Lean_MessageData_ofName(v_recName_1223_);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
v___x_1350_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1349_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
return v___x_1350_;
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_a_1233_);
lean_dec(v_belowName_1225_);
lean_dec(v_nParams_1224_);
v___x_1352_ = l_Lean_MessageData_ofName(v_recName_1223_);
v___x_1353_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1354_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
return v___x_1355_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_belowName_1225_);
lean_dec(v_nParams_1224_);
lean_dec(v_recName_1223_);
v_a_1356_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1232_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1232_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_recName_1223_ = stack[0].m_obj;
lean_object* v_nParams_1224_ = stack[1].m_obj;
lean_object* v_belowName_1225_ = stack[2].m_obj;
lean_object* v_a_1226_ = stack[3].m_obj;
lean_object* v_a_1227_ = stack[4].m_obj;
lean_object* v_a_1228_ = stack[5].m_obj;
lean_object* v_a_1229_ = stack[6].m_obj;
lean_object* v_res_1364_;
v_res_1364_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1223_, v_nParams_1224_, v_belowName_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_);
stack->m_obj
 = v_res_1364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1365_, lean_object* v_nParams_1366_, lean_object* v_belowName_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1365_, v_nParams_1366_, v_belowName_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1373_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1374_, lean_object* v_msg_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1375_ = stack[1].m_obj;
lean_object* v___y_1376_ = stack[2].m_obj;
lean_object* v___y_1377_ = stack[3].m_obj;
lean_object* v___y_1378_ = stack[4].m_obj;
lean_object* v___y_1379_ = stack[5].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_box(0), v_msg_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_msg_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1383_, v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1390_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1391_, uint8_t v_s_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1391_, v_s_1392_, v___y_1394_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1391_ = stack[0].m_obj;
uint8_t v_s_1392_ = stack[1].m_num;
lean_object* v___y_1393_ = stack[2].m_obj;
lean_object* v___y_1394_ = stack[3].m_obj;
lean_object* v___y_1395_ = stack[4].m_obj;
lean_object* v___y_1396_ = stack[5].m_obj;
lean_object* v_res_1399_;
v_res_1399_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1391_, v_s_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
stack->m_obj
 = v_res_1399_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1400_, lean_object* v_s_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
uint8_t v_s_boxed_1407_; lean_object* v_res_1408_; 
v_s_boxed_1407_ = lean_unbox(v_s_1401_);
v_res_1408_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1400_, v_s_boxed_1407_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1408_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1409_, lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1410_ = stack[1].m_obj;
lean_object* v___y_1411_ = stack[2].m_obj;
lean_object* v___y_1412_ = stack[3].m_obj;
lean_object* v___y_1413_ = stack[4].m_obj;
lean_object* v___y_1414_ = stack[5].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_box(0), v_constName_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
stack->m_obj
 = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1418_, lean_object* v_constName_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1418_, v_constName_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
return v_res_1425_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1427_, v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1427_ = stack[1].m_obj;
lean_object* v_constName_1428_ = stack[2].m_obj;
lean_object* v___y_1429_ = stack[3].m_obj;
lean_object* v___y_1430_ = stack[4].m_obj;
lean_object* v___y_1431_ = stack[5].m_obj;
lean_object* v___y_1432_ = stack[6].m_obj;
lean_object* v_res_1435_;
v_res_1435_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_box(0), v_ref_1427_, v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
stack->m_obj
 = v_res_1435_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_ref_1437_, lean_object* v_constName_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1436_, v_ref_1437_, v_constName_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_ref_1437_);
return v_res_1444_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1445_, lean_object* v_ref_1446_, lean_object* v_msg_1447_, lean_object* v_declHint_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1446_, v_msg_1447_, v_declHint_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1446_ = stack[1].m_obj;
lean_object* v_msg_1447_ = stack[2].m_obj;
lean_object* v_declHint_1448_ = stack[3].m_obj;
lean_object* v___y_1449_ = stack[4].m_obj;
lean_object* v___y_1450_ = stack[5].m_obj;
lean_object* v___y_1451_ = stack[6].m_obj;
lean_object* v___y_1452_ = stack[7].m_obj;
lean_object* v_res_1455_;
v_res_1455_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_box(0), v_ref_1446_, v_msg_1447_, v_declHint_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
stack->m_obj
 = v_res_1455_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_ref_1457_, lean_object* v_msg_1458_, lean_object* v_declHint_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1456_, v_ref_1457_, v_msg_1458_, v_declHint_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_ref_1457_);
return v_res_1465_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1466_, lean_object* v_declHint_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1466_, v_declHint_1467_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1466_ = stack[0].m_obj;
lean_object* v_declHint_1467_ = stack[1].m_obj;
lean_object* v___y_1468_ = stack[2].m_obj;
lean_object* v___y_1469_ = stack[3].m_obj;
lean_object* v___y_1470_ = stack[4].m_obj;
lean_object* v___y_1471_ = stack[5].m_obj;
lean_object* v_res_1474_;
v_res_1474_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1466_, v_declHint_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
stack->m_obj
 = v_res_1474_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1475_, lean_object* v_declHint_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1475_, v_declHint_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1482_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1483_, lean_object* v_ref_1484_, lean_object* v_msg_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1484_, v_msg_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1491_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1484_ = stack[1].m_obj;
lean_object* v_msg_1485_ = stack[2].m_obj;
lean_object* v___y_1486_ = stack[3].m_obj;
lean_object* v___y_1487_ = stack[4].m_obj;
lean_object* v___y_1488_ = stack[5].m_obj;
lean_object* v___y_1489_ = stack[6].m_obj;
lean_object* v_res_1492_;
v_res_1492_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_box(0), v_ref_1484_, v_msg_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_ref_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1493_, v_ref_1494_, v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_ref_1494_);
return v_res_1501_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_unsigned_to_nat(32u);
v___x_1503_ = lean_mk_empty_array_with_capacity(v___x_1502_);
v___x_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = ((size_t)5ULL);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_unsigned_to_nat(32u);
v___x_1508_ = lean_mk_empty_array_with_capacity(v___x_1507_);
v___x_1509_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1510_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1506_);
lean_ctor_set(v___x_1510_, 3, v___x_1506_);
lean_ctor_set_usize(v___x_1510_, 4, v___x_1505_);
return v___x_1510_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v_traceState_1514_; lean_object* v_traces_1515_; lean_object* v___x_1516_; lean_object* v_traceState_1517_; lean_object* v_env_1518_; lean_object* v_nextMacroScope_1519_; lean_object* v_ngen_1520_; lean_object* v_auxDeclNGen_1521_; lean_object* v_cache_1522_; lean_object* v_recordedDeps_1523_; lean_object* v_messages_1524_; lean_object* v_infoState_1525_; lean_object* v_snapshotTasks_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1545_; 
v___x_1513_ = lean_st_ref_get(v___y_1511_);
v_traceState_1514_ = lean_ctor_get(v___x_1513_, 4);
lean_inc_ref(v_traceState_1514_);
lean_dec(v___x_1513_);
v_traces_1515_ = lean_ctor_get(v_traceState_1514_, 0);
lean_inc_ref(v_traces_1515_);
lean_dec_ref(v_traceState_1514_);
v___x_1516_ = lean_st_ref_take(v___y_1511_);
v_traceState_1517_ = lean_ctor_get(v___x_1516_, 4);
v_env_1518_ = lean_ctor_get(v___x_1516_, 0);
v_nextMacroScope_1519_ = lean_ctor_get(v___x_1516_, 1);
v_ngen_1520_ = lean_ctor_get(v___x_1516_, 2);
v_auxDeclNGen_1521_ = lean_ctor_get(v___x_1516_, 3);
v_cache_1522_ = lean_ctor_get(v___x_1516_, 5);
v_recordedDeps_1523_ = lean_ctor_get(v___x_1516_, 6);
v_messages_1524_ = lean_ctor_get(v___x_1516_, 7);
v_infoState_1525_ = lean_ctor_get(v___x_1516_, 8);
v_snapshotTasks_1526_ = lean_ctor_get(v___x_1516_, 9);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1528_ = v___x_1516_;
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_snapshotTasks_1526_);
lean_inc(v_infoState_1525_);
lean_inc(v_messages_1524_);
lean_inc(v_recordedDeps_1523_);
lean_inc(v_cache_1522_);
lean_inc(v_traceState_1517_);
lean_inc(v_auxDeclNGen_1521_);
lean_inc(v_ngen_1520_);
lean_inc(v_nextMacroScope_1519_);
lean_inc(v_env_1518_);
lean_dec(v___x_1516_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1545_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint64_t v_tid_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1543_; 
v_tid_1530_ = lean_ctor_get_uint64(v_traceState_1517_, sizeof(void*)*1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_traceState_1517_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_traceState_1517_, 0);
lean_dec(v_unused_1544_);
v___x_1532_ = v_traceState_1517_;
v_isShared_1533_ = v_isSharedCheck_1543_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_traceState_1517_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1543_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1534_);
lean_ctor_set_uint64(v_reuseFailAlloc_1542_, sizeof(void*)*1, v_tid_1530_);
v___x_1536_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 4, v___x_1536_);
v___x_1538_ = v___x_1528_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_env_1518_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_nextMacroScope_1519_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_ngen_1520_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_auxDeclNGen_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v_cache_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 6, v_recordedDeps_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 7, v_messages_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 8, v_infoState_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 9, v_snapshotTasks_1526_);
v___x_1538_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_st_ref_put(v___y_1511_, v___x_1538_);
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_traces_1515_);
return v___x_1540_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1511_ = stack[0].m_obj;
lean_object* v_res_1546_;
v_res_1546_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1511_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1547_);
lean_dec(v___y_1547_);
return v_res_1549_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1550_ = stack[0].m_obj;
lean_object* v___y_1551_ = stack[1].m_obj;
lean_object* v___y_1552_ = stack[2].m_obj;
lean_object* v___y_1553_ = stack[3].m_obj;
lean_object* v_res_1556_;
v_res_1556_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
stack->m_obj
 = v_res_1556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1562_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1563_, lean_object* v_opt_1564_){
_start:
{
lean_object* v_name_1565_; lean_object* v_defValue_1566_; lean_object* v_map_1567_; lean_object* v___x_1568_; 
v_name_1565_ = lean_ctor_get(v_opt_1564_, 0);
v_defValue_1566_ = lean_ctor_get(v_opt_1564_, 1);
v_map_1567_ = lean_ctor_get(v_opts_1563_, 0);
v___x_1568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1567_, v_name_1565_);
if (lean_obj_tag(v___x_1568_) == 0)
{
uint8_t v___x_1569_; 
v___x_1569_ = lean_unbox(v_defValue_1566_);
return v___x_1569_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1570_);
lean_dec_ref_known(v___x_1568_, 1);
if (lean_obj_tag(v_val_1570_) == 1)
{
uint8_t v_v_1571_; 
v_v_1571_ = lean_ctor_get_uint8(v_val_1570_, 0);
lean_dec_ref_known(v_val_1570_, 0);
return v_v_1571_;
}
else
{
uint8_t v___x_1572_; 
lean_dec(v_val_1570_);
v___x_1572_ = lean_unbox(v_defValue_1566_);
return v___x_1572_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_mkBelow_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1563_ = stack[0].m_obj;
lean_object* v_opt_1564_ = stack[1].m_obj;
uint8_t v_res_1573_;
v_res_1573_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1563_, v_opt_1564_);
stack->m_num = v_res_1573_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1574_, lean_object* v_opt_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1574_, v_opt_1575_);
lean_dec_ref(v_opt_1575_);
lean_dec_ref(v_opts_1574_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = l_Lean_MessageData_ofName(v_indName_1578_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT void l_Lean_mkBelow___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1578_ = stack[0].m_obj;
lean_object* v_x_1579_ = stack[1].m_obj;
lean_object* v___y_1580_ = stack[2].m_obj;
lean_object* v___y_1581_ = stack[3].m_obj;
lean_object* v___y_1582_ = stack[4].m_obj;
lean_object* v___y_1583_ = stack[5].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_Lean_mkBelow___lam__0(v_indName_1578_, v_x_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_mkBelow___lam__0(v_indName_1588_, v_x_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec_ref(v_x_1589_);
return v_res_1595_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1596_){
_start:
{
if (lean_obj_tag(v_e_1596_) == 0)
{
uint8_t v___x_1597_; 
v___x_1597_ = 2;
return v___x_1597_;
}
else
{
uint8_t v___x_1598_; 
v___x_1598_ = 0;
return v___x_1598_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1596_ = stack[0].m_obj;
uint8_t v_res_1599_;
v_res_1599_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1596_);
stack->m_num = v_res_1599_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1600_){
_start:
{
uint8_t v_res_1601_; lean_object* v_r_1602_; 
v_res_1601_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1600_);
lean_dec_ref(v_e_1600_);
v_r_1602_ = lean_box(v_res_1601_);
return v_r_1602_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1603_){
_start:
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v_x_1603_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_x_1603_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
v_a_1613_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v_x_1603_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v_x_1603_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 0);
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1603_ = stack[0].m_obj;
lean_object* v_res_1621_;
v_res_1621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1603_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1625_, lean_object* v_opt_1626_){
_start:
{
lean_object* v_name_1627_; lean_object* v_defValue_1628_; lean_object* v_map_1629_; lean_object* v___x_1630_; 
v_name_1627_ = lean_ctor_get(v_opt_1626_, 0);
v_defValue_1628_ = lean_ctor_get(v_opt_1626_, 1);
v_map_1629_ = lean_ctor_get(v_opts_1625_, 0);
v___x_1630_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1629_, v_name_1627_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_inc(v_defValue_1628_);
return v_defValue_1628_;
}
else
{
lean_object* v_val_1631_; 
v_val_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_val_1631_);
lean_dec_ref_known(v___x_1630_, 1);
if (lean_obj_tag(v_val_1631_) == 3)
{
lean_object* v_v_1632_; 
v_v_1632_ = lean_ctor_get(v_val_1631_, 0);
lean_inc(v_v_1632_);
lean_dec_ref_known(v_val_1631_, 1);
return v_v_1632_;
}
else
{
lean_dec(v_val_1631_);
lean_inc(v_defValue_1628_);
return v_defValue_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1633_, lean_object* v_opt_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1633_, v_opt_1634_);
lean_dec_ref(v_opt_1634_);
lean_dec_ref(v_opts_1633_);
return v_res_1635_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1636_, size_t v_i_1637_, lean_object* v_bs_1638_){
_start:
{
uint8_t v___x_1639_; 
v___x_1639_ = lean_usize_dec_lt(v_i_1637_, v_sz_1636_);
if (v___x_1639_ == 0)
{
return v_bs_1638_;
}
else
{
lean_object* v_v_1640_; lean_object* v_msg_1641_; lean_object* v___x_1642_; lean_object* v_bs_x27_1643_; size_t v___x_1644_; size_t v___x_1645_; lean_object* v___x_1646_; 
v_v_1640_ = lean_array_uget_borrowed(v_bs_1638_, v_i_1637_);
v_msg_1641_ = lean_ctor_get(v_v_1640_, 1);
lean_inc_ref(v_msg_1641_);
v___x_1642_ = lean_unsigned_to_nat(0u);
v_bs_x27_1643_ = lean_array_uset(v_bs_1638_, v_i_1637_, v___x_1642_);
v___x_1644_ = ((size_t)1ULL);
v___x_1645_ = lean_usize_add(v_i_1637_, v___x_1644_);
v___x_1646_ = lean_array_uset(v_bs_x27_1643_, v_i_1637_, v_msg_1641_);
v_i_1637_ = v___x_1645_;
v_bs_1638_ = v___x_1646_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1636_ = stack[0].m_num;
size_t v_i_1637_ = stack[1].m_num;
lean_object* v_bs_1638_ = stack[2].m_obj;
lean_object* v_res_1648_;
v_res_1648_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1636_, v_i_1637_, v_bs_1638_);
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1649_, lean_object* v_i_1650_, lean_object* v_bs_1651_){
_start:
{
size_t v_sz_boxed_1652_; size_t v_i_boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1652_ = lean_unbox_usize(v_sz_1649_);
lean_dec(v_sz_1649_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1652_, v_i_boxed_1653_, v_bs_1651_);
return v_res_1654_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1655_, lean_object* v_data_1656_, lean_object* v_ref_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_toCold_1664_; lean_object* v_currRecDepth_1665_; lean_object* v_ref_1666_; uint16_t v_optionFlags_1667_; uint8_t v_suppressElabErrors_1668_; uint8_t v_isRecordingDeps_1669_; lean_object* v_ref_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_traceState_1673_; lean_object* v_traces_1674_; lean_object* v___x_1675_; size_t v_sz_1676_; size_t v___x_1677_; lean_object* v___x_1678_; lean_object* v_msg_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1719_; 
v_toCold_1664_ = lean_ctor_get(v___y_1661_, 0);
v_currRecDepth_1665_ = lean_ctor_get(v___y_1661_, 1);
v_ref_1666_ = lean_ctor_get(v___y_1661_, 2);
v_optionFlags_1667_ = lean_ctor_get_uint16(v___y_1661_, sizeof(void*)*3);
v_suppressElabErrors_1668_ = lean_ctor_get_uint8(v___y_1661_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1669_ = lean_ctor_get_uint8(v___y_1661_, sizeof(void*)*3 + 3);
v_ref_1670_ = l_Lean_replaceRef(v_ref_1657_, v_ref_1666_);
lean_inc(v_currRecDepth_1665_);
lean_inc_ref(v_toCold_1664_);
v___x_1671_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1671_, 0, v_toCold_1664_);
lean_ctor_set(v___x_1671_, 1, v_currRecDepth_1665_);
lean_ctor_set(v___x_1671_, 2, v_ref_1670_);
lean_ctor_set_uint16(v___x_1671_, sizeof(void*)*3, v_optionFlags_1667_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3 + 2, v_suppressElabErrors_1668_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3 + 3, v_isRecordingDeps_1669_);
v___x_1672_ = lean_st_ref_get(v___y_1662_);
v_traceState_1673_ = lean_ctor_get(v___x_1672_, 4);
lean_inc_ref(v_traceState_1673_);
lean_dec(v___x_1672_);
v_traces_1674_ = lean_ctor_get(v_traceState_1673_, 0);
lean_inc_ref(v_traces_1674_);
lean_dec_ref(v_traceState_1673_);
v___x_1675_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1674_);
lean_dec_ref(v_traces_1674_);
v_sz_1676_ = lean_array_size(v___x_1675_);
v___x_1677_ = ((size_t)0ULL);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1676_, v___x_1677_, v___x_1675_);
v_msg_1679_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1679_, 0, v_data_1656_);
lean_ctor_set(v_msg_1679_, 1, v_msg_1658_);
lean_ctor_set(v_msg_1679_, 2, v___x_1678_);
v___x_1680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1679_, v___y_1659_, v___y_1660_, v___x_1671_, v___y_1662_);
lean_dec_ref_known(v___x_1671_, 3);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1719_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1719_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v_traceState_1686_; lean_object* v_env_1687_; lean_object* v_nextMacroScope_1688_; lean_object* v_ngen_1689_; lean_object* v_auxDeclNGen_1690_; lean_object* v_cache_1691_; lean_object* v_recordedDeps_1692_; lean_object* v_messages_1693_; lean_object* v_infoState_1694_; lean_object* v_snapshotTasks_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1718_; 
v___x_1685_ = lean_st_ref_take(v___y_1662_);
v_traceState_1686_ = lean_ctor_get(v___x_1685_, 4);
v_env_1687_ = lean_ctor_get(v___x_1685_, 0);
v_nextMacroScope_1688_ = lean_ctor_get(v___x_1685_, 1);
v_ngen_1689_ = lean_ctor_get(v___x_1685_, 2);
v_auxDeclNGen_1690_ = lean_ctor_get(v___x_1685_, 3);
v_cache_1691_ = lean_ctor_get(v___x_1685_, 5);
v_recordedDeps_1692_ = lean_ctor_get(v___x_1685_, 6);
v_messages_1693_ = lean_ctor_get(v___x_1685_, 7);
v_infoState_1694_ = lean_ctor_get(v___x_1685_, 8);
v_snapshotTasks_1695_ = lean_ctor_get(v___x_1685_, 9);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1697_ = v___x_1685_;
v_isShared_1698_ = v_isSharedCheck_1718_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_snapshotTasks_1695_);
lean_inc(v_infoState_1694_);
lean_inc(v_messages_1693_);
lean_inc(v_recordedDeps_1692_);
lean_inc(v_cache_1691_);
lean_inc(v_traceState_1686_);
lean_inc(v_auxDeclNGen_1690_);
lean_inc(v_ngen_1689_);
lean_inc(v_nextMacroScope_1688_);
lean_inc(v_env_1687_);
lean_dec(v___x_1685_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1718_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint64_t v_tid_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1716_; 
v_tid_1699_ = lean_ctor_get_uint64(v_traceState_1686_, sizeof(void*)*1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_traceState_1686_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_traceState_1686_, 0);
lean_dec(v_unused_1717_);
v___x_1701_ = v_traceState_1686_;
v_isShared_1702_ = v_isSharedCheck_1716_;
goto v_resetjp_1700_;
}
else
{
lean_dec(v_traceState_1686_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1716_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1703_ = lean_box(0);
v___x_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1704_, 0, v_ref_1657_);
lean_ctor_set(v___x_1704_, 1, v_a_1681_);
v___x_1705_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1655_, v___x_1704_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1705_);
v___x_1707_ = v___x_1701_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1705_);
lean_ctor_set_uint64(v_reuseFailAlloc_1715_, sizeof(void*)*1, v_tid_1699_);
v___x_1707_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 4, v___x_1707_);
v___x_1709_ = v___x_1697_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_env_1687_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_nextMacroScope_1688_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_ngen_1689_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_auxDeclNGen_1690_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1714_, 5, v_cache_1691_);
lean_ctor_set(v_reuseFailAlloc_1714_, 6, v_recordedDeps_1692_);
lean_ctor_set(v_reuseFailAlloc_1714_, 7, v_messages_1693_);
lean_ctor_set(v_reuseFailAlloc_1714_, 8, v_infoState_1694_);
lean_ctor_set(v_reuseFailAlloc_1714_, 9, v_snapshotTasks_1695_);
v___x_1709_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_st_ref_put(v___y_1662_, v___x_1709_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1703_);
v___x_1712_ = v___x_1683_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1703_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1655_ = stack[0].m_obj;
lean_object* v_data_1656_ = stack[1].m_obj;
lean_object* v_ref_1657_ = stack[2].m_obj;
lean_object* v_msg_1658_ = stack[3].m_obj;
lean_object* v___y_1659_ = stack[4].m_obj;
lean_object* v___y_1660_ = stack[5].m_obj;
lean_object* v___y_1661_ = stack[6].m_obj;
lean_object* v___y_1662_ = stack[7].m_obj;
lean_object* v_res_1720_;
v_res_1720_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1655_, v_data_1656_, v_ref_1657_, v_msg_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
stack->m_obj
 = v_res_1720_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1721_, lean_object* v_data_1722_, lean_object* v_ref_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1721_, v_data_1722_, v_ref_1723_, v_msg_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1730_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1731_; double v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_float_of_nat(v___x_1731_);
return v___x_1732_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1735_ = l_Lean_stringToMessageData(v___x_1734_);
return v___x_1735_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1736_; double v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(1000u);
v___x_1737_ = lean_float_of_nat(v___x_1736_);
return v___x_1737_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1738_, uint8_t v_collapsed_1739_, lean_object* v_tag_1740_, lean_object* v_opts_1741_, uint8_t v_clsEnabled_1742_, lean_object* v_oldTraces_1743_, lean_object* v_msg_1744_, lean_object* v_resStartStop_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v_data_1756_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; lean_object* v___y_1764_; lean_object* v_a_1765_; uint8_t v___y_1780_; double v___y_1812_; 
v_fst_1751_ = lean_ctor_get(v_resStartStop_1745_, 0);
lean_inc(v_fst_1751_);
v_snd_1752_ = lean_ctor_get(v_resStartStop_1745_, 1);
lean_inc(v_snd_1752_);
lean_dec_ref(v_resStartStop_1745_);
v_fst_1759_ = lean_ctor_get(v_snd_1752_, 0);
lean_inc(v_fst_1759_);
v_snd_1760_ = lean_ctor_get(v_snd_1752_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_snd_1752_);
v___x_1761_ = l_Lean_trace_profiler;
v___x_1762_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1741_, v___x_1761_);
if (v___x_1762_ == 0)
{
v___y_1780_ = v___x_1762_;
goto v___jp_1779_;
}
else
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1818_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1741_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; double v___x_1821_; double v___x_1822_; double v___x_1823_; 
v___x_1819_ = l_Lean_trace_profiler_threshold;
v___x_1820_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1741_, v___x_1819_);
v___x_1821_ = lean_float_of_nat(v___x_1820_);
v___x_1822_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1823_ = lean_float_div(v___x_1821_, v___x_1822_);
v___y_1812_ = v___x_1823_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; double v___x_1826_; 
v___x_1824_ = l_Lean_trace_profiler_threshold;
v___x_1825_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1741_, v___x_1824_);
v___x_1826_ = lean_float_of_nat(v___x_1825_);
v___y_1812_ = v___x_1826_;
goto v___jp_1811_;
}
}
v___jp_1753_:
{
lean_object* v___x_1757_; 
lean_inc(v___y_1755_);
v___x_1757_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1743_, v_data_1756_, v___y_1755_, v___y_1754_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; 
lean_dec_ref_known(v___x_1757_, 1);
v___x_1758_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1751_);
return v___x_1758_;
}
else
{
lean_dec(v_fst_1751_);
return v___x_1757_;
}
}
v___jp_1763_:
{
uint8_t v_result_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; double v___x_1769_; lean_object* v_data_1770_; 
v_result_1766_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1751_);
v___x_1767_ = lean_box(v_result_1766_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
v___x_1769_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1740_);
lean_inc_ref(v___x_1768_);
lean_inc(v_cls_1738_);
v_data_1770_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1770_, 0, v_cls_1738_);
lean_ctor_set(v_data_1770_, 1, v___x_1768_);
lean_ctor_set(v_data_1770_, 2, v_tag_1740_);
lean_ctor_set_float(v_data_1770_, sizeof(void*)*3, v___x_1769_);
lean_ctor_set_float(v_data_1770_, sizeof(void*)*3 + 8, v___x_1769_);
lean_ctor_set_uint8(v_data_1770_, sizeof(void*)*3 + 16, v_collapsed_1739_);
if (v___x_1762_ == 0)
{
lean_dec_ref_known(v___x_1768_, 1);
lean_dec(v_snd_1760_);
lean_dec(v_fst_1759_);
lean_dec_ref(v_tag_1740_);
lean_dec(v_cls_1738_);
v___y_1754_ = v_a_1765_;
v___y_1755_ = v___y_1764_;
v_data_1756_ = v_data_1770_;
goto v___jp_1753_;
}
else
{
lean_object* v_data_1771_; double v___x_1772_; double v___x_1773_; 
lean_dec_ref_known(v_data_1770_, 3);
v_data_1771_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1771_, 0, v_cls_1738_);
lean_ctor_set(v_data_1771_, 1, v___x_1768_);
lean_ctor_set(v_data_1771_, 2, v_tag_1740_);
v___x_1772_ = lean_unbox_float(v_fst_1759_);
lean_dec(v_fst_1759_);
lean_ctor_set_float(v_data_1771_, sizeof(void*)*3, v___x_1772_);
v___x_1773_ = lean_unbox_float(v_snd_1760_);
lean_dec(v_snd_1760_);
lean_ctor_set_float(v_data_1771_, sizeof(void*)*3 + 8, v___x_1773_);
lean_ctor_set_uint8(v_data_1771_, sizeof(void*)*3 + 16, v_collapsed_1739_);
v___y_1754_ = v_a_1765_;
v___y_1755_ = v___y_1764_;
v_data_1756_ = v_data_1771_;
goto v___jp_1753_;
}
}
v___jp_1774_:
{
lean_object* v_ref_1775_; lean_object* v___x_1776_; 
v_ref_1775_ = lean_ctor_get(v___y_1748_, 2);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v___y_1747_);
lean_inc_ref(v___y_1746_);
lean_inc(v_fst_1751_);
v___x_1776_ = lean_apply_6(v_msg_1744_, v_fst_1751_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, lean_box(0));
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___y_1764_ = v_ref_1775_;
v_a_1765_ = v_a_1777_;
goto v___jp_1763_;
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1764_ = v_ref_1775_;
v_a_1765_ = v___x_1778_;
goto v___jp_1763_;
}
}
v___jp_1779_:
{
if (v_clsEnabled_1742_ == 0)
{
if (v___y_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v_traceState_1782_; lean_object* v_env_1783_; lean_object* v_nextMacroScope_1784_; lean_object* v_ngen_1785_; lean_object* v_auxDeclNGen_1786_; lean_object* v_cache_1787_; lean_object* v_recordedDeps_1788_; lean_object* v_messages_1789_; lean_object* v_infoState_1790_; lean_object* v_snapshotTasks_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v_snd_1760_);
lean_dec(v_fst_1759_);
lean_dec_ref(v_msg_1744_);
lean_dec_ref(v_tag_1740_);
lean_dec(v_cls_1738_);
v___x_1781_ = lean_st_ref_take(v___y_1749_);
v_traceState_1782_ = lean_ctor_get(v___x_1781_, 4);
v_env_1783_ = lean_ctor_get(v___x_1781_, 0);
v_nextMacroScope_1784_ = lean_ctor_get(v___x_1781_, 1);
v_ngen_1785_ = lean_ctor_get(v___x_1781_, 2);
v_auxDeclNGen_1786_ = lean_ctor_get(v___x_1781_, 3);
v_cache_1787_ = lean_ctor_get(v___x_1781_, 5);
v_recordedDeps_1788_ = lean_ctor_get(v___x_1781_, 6);
v_messages_1789_ = lean_ctor_get(v___x_1781_, 7);
v_infoState_1790_ = lean_ctor_get(v___x_1781_, 8);
v_snapshotTasks_1791_ = lean_ctor_get(v___x_1781_, 9);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1793_ = v___x_1781_;
v_isShared_1794_ = v_isSharedCheck_1810_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snapshotTasks_1791_);
lean_inc(v_infoState_1790_);
lean_inc(v_messages_1789_);
lean_inc(v_recordedDeps_1788_);
lean_inc(v_cache_1787_);
lean_inc(v_traceState_1782_);
lean_inc(v_auxDeclNGen_1786_);
lean_inc(v_ngen_1785_);
lean_inc(v_nextMacroScope_1784_);
lean_inc(v_env_1783_);
lean_dec(v___x_1781_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1810_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint64_t v_tid_1795_; lean_object* v_traces_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1809_; 
v_tid_1795_ = lean_ctor_get_uint64(v_traceState_1782_, sizeof(void*)*1);
v_traces_1796_ = lean_ctor_get(v_traceState_1782_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_traceState_1782_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1798_ = v_traceState_1782_;
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_traces_1796_);
lean_dec(v_traceState_1782_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1809_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1800_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1743_, v_traces_1796_);
lean_dec_ref(v_traces_1796_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1802_ = v___x_1798_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1800_);
lean_ctor_set_uint64(v_reuseFailAlloc_1808_, sizeof(void*)*1, v_tid_1795_);
v___x_1802_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 4, v___x_1802_);
v___x_1804_ = v___x_1793_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_env_1783_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_nextMacroScope_1784_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1785_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1786_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_cache_1787_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_recordedDeps_1788_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_messages_1789_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_infoState_1790_);
lean_ctor_set(v_reuseFailAlloc_1807_, 9, v_snapshotTasks_1791_);
v___x_1804_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1805_ = lean_st_ref_put(v___y_1749_, v___x_1804_);
v___x_1806_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1751_);
return v___x_1806_;
}
}
}
}
}
else
{
goto v___jp_1774_;
}
}
else
{
goto v___jp_1774_;
}
}
v___jp_1811_:
{
double v___x_1813_; double v___x_1814_; double v___x_1815_; uint8_t v___x_1816_; 
v___x_1813_ = lean_unbox_float(v_snd_1760_);
v___x_1814_ = lean_unbox_float(v_fst_1759_);
v___x_1815_ = lean_float_sub(v___x_1813_, v___x_1814_);
v___x_1816_ = lean_float_decLt(v___y_1812_, v___x_1815_);
v___y_1780_ = v___x_1816_;
goto v___jp_1779_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1738_ = stack[0].m_obj;
uint8_t v_collapsed_1739_ = stack[1].m_num;
lean_object* v_tag_1740_ = stack[2].m_obj;
lean_object* v_opts_1741_ = stack[3].m_obj;
uint8_t v_clsEnabled_1742_ = stack[4].m_num;
lean_object* v_oldTraces_1743_ = stack[5].m_obj;
lean_object* v_msg_1744_ = stack[6].m_obj;
lean_object* v_resStartStop_1745_ = stack[7].m_obj;
lean_object* v___y_1746_ = stack[8].m_obj;
lean_object* v___y_1747_ = stack[9].m_obj;
lean_object* v___y_1748_ = stack[10].m_obj;
lean_object* v___y_1749_ = stack[11].m_obj;
lean_object* v_res_1827_;
v_res_1827_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1738_, v_collapsed_1739_, v_tag_1740_, v_opts_1741_, v_clsEnabled_1742_, v_oldTraces_1743_, v_msg_1744_, v_resStartStop_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
stack->m_obj
 = v_res_1827_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1828_, lean_object* v_collapsed_1829_, lean_object* v_tag_1830_, lean_object* v_opts_1831_, lean_object* v_clsEnabled_1832_, lean_object* v_oldTraces_1833_, lean_object* v_msg_1834_, lean_object* v_resStartStop_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
uint8_t v_collapsed_boxed_1841_; uint8_t v_clsEnabled_boxed_1842_; lean_object* v_res_1843_; 
v_collapsed_boxed_1841_ = lean_unbox(v_collapsed_1829_);
v_clsEnabled_boxed_1842_ = lean_unbox(v_clsEnabled_1832_);
v_res_1843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1828_, v_collapsed_boxed_1841_, v_tag_1830_, v_opts_1831_, v_clsEnabled_boxed_1842_, v_oldTraces_1833_, v_msg_1834_, v_resStartStop_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v_opts_1831_);
return v_res_1843_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1844_, lean_object* v___x_1845_, lean_object* v___x_1846_, lean_object* v___x_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_lt(v_a_1848_, v_upperBound_1844_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec(v_a_1848_);
lean_dec(v___x_1847_);
lean_dec(v___x_1846_);
lean_dec(v___x_1845_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_b_1849_);
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_a_1848_, v___x_1858_);
lean_dec(v_a_1848_);
lean_inc_n(v___x_1859_, 2);
lean_inc(v___x_1845_);
v___x_1860_ = lean_name_append_index_after(v___x_1845_, v___x_1859_);
lean_inc(v___x_1846_);
v___x_1861_ = lean_name_append_index_after(v___x_1846_, v___x_1859_);
lean_inc(v___x_1847_);
v___x_1862_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1860_, v___x_1847_, v___x_1861_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_dec_ref_known(v___x_1862_, 1);
v_a_1848_ = v___x_1859_;
v_b_1849_ = v___x_1857_;
goto _start;
}
else
{
lean_dec(v___x_1859_);
lean_dec(v___x_1847_);
lean_dec(v___x_1846_);
lean_dec(v___x_1845_);
return v___x_1862_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1844_ = stack[0].m_obj;
lean_object* v___x_1845_ = stack[1].m_obj;
lean_object* v___x_1846_ = stack[2].m_obj;
lean_object* v___x_1847_ = stack[3].m_obj;
lean_object* v_a_1848_ = stack[4].m_obj;
lean_object* v_b_1849_ = stack[5].m_obj;
lean_object* v___y_1850_ = stack[6].m_obj;
lean_object* v___y_1851_ = stack[7].m_obj;
lean_object* v___y_1852_ = stack[8].m_obj;
lean_object* v___y_1853_ = stack[9].m_obj;
lean_object* v_res_1864_;
v_res_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1844_, v___x_1845_, v___x_1846_, v___x_1847_, v_a_1848_, v_b_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
stack->m_obj
 = v_res_1864_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1865_, lean_object* v___x_1866_, lean_object* v___x_1867_, lean_object* v___x_1868_, lean_object* v_a_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1865_, v___x_1866_, v___x_1867_, v___x_1868_, v_a_1869_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v_upperBound_1865_);
return v_res_1876_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1887_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1888_ = l_Lean_Name_append(v___x_1887_, v___x_1886_);
return v___x_1888_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1889_; double v___x_1890_; 
v___x_1889_ = lean_unsigned_to_nat(1000000000u);
v___x_1890_ = lean_float_of_nat(v___x_1889_);
return v___x_1890_;
}
}
lean_object* l_Lean_mkBelow(lean_object* v_indName_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_toCold_1897_; lean_object* v_options_1898_; lean_object* v_inheritedTraceOptions_1899_; uint8_t v_hasTrace_1900_; lean_object* v___x_1901_; 
v_toCold_1897_ = lean_ctor_get(v_a_1894_, 0);
v_options_1898_ = lean_ctor_get(v_toCold_1897_, 2);
v_inheritedTraceOptions_1899_ = lean_ctor_get(v_toCold_1897_, 11);
v_hasTrace_1900_ = lean_ctor_get_uint8(v_options_1898_, sizeof(void*)*1);
v___x_1901_ = lean_box(0);
if (v_hasTrace_1900_ == 0)
{
lean_object* v___x_1902_; 
lean_inc(v_indName_1891_);
v___x_1902_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1966_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1966_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1966_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
if (lean_obj_tag(v_a_1903_) == 5)
{
lean_object* v_val_1907_; uint8_t v_isRec_1908_; 
v_val_1907_ = lean_ctor_get(v_a_1903_, 0);
lean_inc_ref(v_val_1907_);
lean_dec_ref_known(v_a_1903_, 1);
v_isRec_1908_ = lean_ctor_get_uint8(v_val_1907_, sizeof(void*)*6);
if (v_isRec_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec_ref(v_val_1907_);
lean_dec(v_indName_1891_);
v___x_1909_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1909_);
v___x_1911_ = v___x_1905_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v_toConstantVal_1913_; lean_object* v_numParams_1914_; lean_object* v_all_1915_; lean_object* v_numNested_1916_; lean_object* v_type_1917_; lean_object* v___x_1918_; 
lean_del_object(v___x_1905_);
v_toConstantVal_1913_ = lean_ctor_get(v_val_1907_, 0);
lean_inc_ref(v_toConstantVal_1913_);
v_numParams_1914_ = lean_ctor_get(v_val_1907_, 1);
lean_inc(v_numParams_1914_);
v_all_1915_ = lean_ctor_get(v_val_1907_, 3);
lean_inc(v_all_1915_);
v_numNested_1916_ = lean_ctor_get(v_val_1907_, 5);
lean_inc(v_numNested_1916_);
lean_dec_ref(v_val_1907_);
v_type_1917_ = lean_ctor_get(v_toConstantVal_1913_, 2);
lean_inc_ref(v_type_1917_);
lean_dec_ref(v_toConstantVal_1913_);
v___x_1918_ = l_Lean_Meta_isPropFormerType(v_type_1917_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1953_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1953_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_unbox(v_a_1919_);
lean_dec(v_a_1919_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_del_object(v___x_1921_);
lean_inc_n(v_indName_1891_, 2);
v___x_1924_ = l_Lean_mkRecName(v_indName_1891_);
v___x_1925_ = l_Lean_mkBelowName(v_indName_1891_);
lean_inc(v___x_1925_);
lean_inc(v_numParams_1914_);
lean_inc(v___x_1924_);
v___x_1926_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1924_, v_numParams_1914_, v___x_1925_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1947_; 
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1926_, 0);
lean_dec(v_unused_1948_);
v___x_1928_ = v___x_1926_;
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
else
{
lean_dec(v___x_1926_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1947_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = l_List_get_x21Internal___redArg(v___x_1901_, v_all_1915_, v___x_1930_);
lean_dec(v_all_1915_);
v___x_1932_ = lean_name_eq(v___x_1931_, v_indName_1891_);
lean_dec(v_indName_1891_);
lean_dec(v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
lean_dec(v_numNested_1916_);
lean_dec(v_numParams_1914_);
v___x_1933_ = lean_box(0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1933_);
v___x_1935_ = v___x_1928_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1928_);
v___x_1937_ = lean_box(0);
v___x_1938_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1916_, v___x_1924_, v___x_1925_, v_numParams_1914_, v___x_1930_, v___x_1937_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_numNested_1916_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1938_, 0);
lean_dec(v_unused_1946_);
v___x_1940_ = v___x_1938_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1937_);
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1937_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
return v___x_1938_;
}
}
}
}
else
{
lean_dec(v___x_1925_);
lean_dec(v___x_1924_);
lean_dec(v_numNested_1916_);
lean_dec(v_all_1915_);
lean_dec(v_numParams_1914_);
lean_dec(v_indName_1891_);
return v___x_1926_;
}
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
lean_dec(v_numNested_1916_);
lean_dec(v_all_1915_);
lean_dec(v_numParams_1914_);
lean_dec(v_indName_1891_);
v___x_1949_ = lean_box(0);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1949_);
v___x_1951_ = v___x_1921_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_numNested_1916_);
lean_dec(v_all_1915_);
lean_dec(v_numParams_1914_);
lean_dec(v_indName_1891_);
v_a_1954_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1918_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1918_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
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
return v___x_1959_;
}
}
}
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_a_1903_);
lean_dec(v_indName_1891_);
v___x_1962_ = lean_box(0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1962_);
v___x_1964_ = v___x_1905_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_indName_1891_);
v_a_1967_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1902_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1902_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v_a_1983_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v_a_1998_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v_a_2003_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v_a_2008_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v_a_2020_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v_a_2025_; 
lean_inc(v_indName_1891_);
v___f_1975_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1975_, 0, v_indName_1891_);
v___x_1976_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1977_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1978_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1979_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1899_, v_options_1898_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2092_ = l_Lean_trace_profiler;
v___x_2093_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1898_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec_ref(v___f_1975_);
lean_inc(v_indName_1891_);
v___x_2094_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2158_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2158_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2158_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
if (lean_obj_tag(v_a_2095_) == 5)
{
lean_object* v_val_2099_; uint8_t v_isRec_2100_; 
v_val_2099_ = lean_ctor_get(v_a_2095_, 0);
lean_inc_ref(v_val_2099_);
lean_dec_ref_known(v_a_2095_, 1);
v_isRec_2100_ = lean_ctor_get_uint8(v_val_2099_, sizeof(void*)*6);
if (v_isRec_2100_ == 0)
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_dec_ref(v_val_2099_);
lean_dec(v_indName_1891_);
v___x_2101_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
else
{
lean_object* v_toConstantVal_2105_; lean_object* v_numParams_2106_; lean_object* v_all_2107_; lean_object* v_numNested_2108_; lean_object* v_type_2109_; lean_object* v___x_2110_; 
lean_del_object(v___x_2097_);
v_toConstantVal_2105_ = lean_ctor_get(v_val_2099_, 0);
lean_inc_ref(v_toConstantVal_2105_);
v_numParams_2106_ = lean_ctor_get(v_val_2099_, 1);
lean_inc(v_numParams_2106_);
v_all_2107_ = lean_ctor_get(v_val_2099_, 3);
lean_inc(v_all_2107_);
v_numNested_2108_ = lean_ctor_get(v_val_2099_, 5);
lean_inc(v_numNested_2108_);
lean_dec_ref(v_val_2099_);
v_type_2109_ = lean_ctor_get(v_toConstantVal_2105_, 2);
lean_inc_ref(v_type_2109_);
lean_dec_ref(v_toConstantVal_2105_);
v___x_2110_ = l_Lean_Meta_isPropFormerType(v_type_2109_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2145_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2145_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2145_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
uint8_t v___x_2115_; 
v___x_2115_ = lean_unbox(v_a_2111_);
lean_dec(v_a_2111_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_del_object(v___x_2113_);
lean_inc_n(v_indName_1891_, 2);
v___x_2116_ = l_Lean_mkRecName(v_indName_1891_);
v___x_2117_ = l_Lean_mkBelowName(v_indName_1891_);
lean_inc(v___x_2117_);
lean_inc(v_numParams_2106_);
lean_inc(v___x_2116_);
v___x_2118_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2116_, v_numParams_2106_, v___x_2117_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2139_; 
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2140_);
v___x_2120_ = v___x_2118_;
v_isShared_2121_ = v_isSharedCheck_2139_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v___x_2118_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2139_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = l_List_get_x21Internal___redArg(v___x_1901_, v_all_2107_, v___x_2122_);
lean_dec(v_all_2107_);
v___x_2124_ = lean_name_eq(v___x_2123_, v_indName_1891_);
lean_dec(v_indName_1891_);
lean_dec(v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
lean_dec(v___x_2117_);
lean_dec(v___x_2116_);
lean_dec(v_numNested_2108_);
lean_dec(v_numParams_2106_);
v___x_2125_ = lean_box(0);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2125_);
v___x_2127_ = v___x_2120_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_del_object(v___x_2120_);
v___x_2129_ = lean_box(0);
v___x_2130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2108_, v___x_2116_, v___x_2117_, v_numParams_2106_, v___x_2122_, v___x_2129_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_numNested_2108_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2130_, 0);
lean_dec(v_unused_2138_);
v___x_2132_ = v___x_2130_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v___x_2130_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2129_);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2129_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
return v___x_2130_;
}
}
}
}
else
{
lean_dec(v___x_2117_);
lean_dec(v___x_2116_);
lean_dec(v_numNested_2108_);
lean_dec(v_all_2107_);
lean_dec(v_numParams_2106_);
lean_dec(v_indName_1891_);
return v___x_2118_;
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec(v_numNested_2108_);
lean_dec(v_all_2107_);
lean_dec(v_numParams_2106_);
lean_dec(v_indName_1891_);
v___x_2141_ = lean_box(0);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2141_);
v___x_2143_ = v___x_2113_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_numNested_2108_);
lean_dec(v_all_2107_);
lean_dec(v_numParams_2106_);
lean_dec(v_indName_1891_);
v_a_2146_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2110_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2110_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec(v_a_2095_);
lean_dec(v_indName_1891_);
v___x_2154_ = lean_box(0);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2154_);
v___x_2156_ = v___x_2097_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_indName_1891_);
v_a_2159_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2094_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2094_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
goto v___jp_2027_;
}
}
else
{
goto v___jp_2027_;
}
v___jp_1980_:
{
lean_object* v___x_1984_; double v___x_1985_; double v___x_1986_; double v___x_1987_; double v___x_1988_; double v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1984_ = lean_io_mono_nanos_now();
v___x_1985_ = lean_float_of_nat(v___y_1982_);
v___x_1986_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1987_ = lean_float_div(v___x_1985_, v___x_1986_);
v___x_1988_ = lean_float_of_nat(v___x_1984_);
v___x_1989_ = lean_float_div(v___x_1988_, v___x_1986_);
v___x_1990_ = lean_box_float(v___x_1987_);
v___x_1991_ = lean_box_float(v___x_1989_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v_a_1983_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1976_, v_hasTrace_1900_, v___x_1977_, v_options_1898_, v___x_1979_, v___y_1981_, v___f_1975_, v___x_1993_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_1994_;
}
v___jp_1995_:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1998_);
v___y_1981_ = v___y_1996_;
v___y_1982_ = v___y_1997_;
v_a_1983_ = v___x_1999_;
goto v___jp_1980_;
}
v___jp_2000_:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_a_2003_);
v___y_1981_ = v___y_2001_;
v___y_1982_ = v___y_2002_;
v_a_1983_ = v___x_2004_;
goto v___jp_1980_;
}
v___jp_2005_:
{
lean_object* v___x_2009_; double v___x_2010_; double v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2009_ = lean_io_get_num_heartbeats();
v___x_2010_ = lean_float_of_nat(v___y_2007_);
v___x_2011_ = lean_float_of_nat(v___x_2009_);
v___x_2012_ = lean_box_float(v___x_2010_);
v___x_2013_ = lean_box_float(v___x_2011_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_a_2008_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1976_, v_hasTrace_1900_, v___x_1977_, v_options_1898_, v___x_1979_, v___y_2006_, v___f_1975_, v___x_2015_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
return v___x_2016_;
}
v___jp_2017_:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2020_);
v___y_2006_ = v___y_2018_;
v___y_2007_ = v___y_2019_;
v_a_2008_ = v___x_2021_;
goto v___jp_2005_;
}
v___jp_2022_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_a_2025_);
v___y_2006_ = v___y_2023_;
v___y_2007_ = v___y_2024_;
v_a_2008_ = v___x_2026_;
goto v___jp_2005_;
}
v___jp_2027_:
{
lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1895_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2028_);
v___x_2030_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2031_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1898_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1891_);
v___x_2033_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
if (lean_obj_tag(v_a_2034_) == 5)
{
lean_object* v_val_2035_; uint8_t v_isRec_2036_; 
v_val_2035_ = lean_ctor_get(v_a_2034_, 0);
lean_inc_ref(v_val_2035_);
lean_dec_ref_known(v_a_2034_, 1);
v_isRec_2036_ = lean_ctor_get_uint8(v_val_2035_, sizeof(void*)*6);
if (v_isRec_2036_ == 0)
{
lean_object* v___x_2037_; 
lean_dec_ref(v_val_2035_);
lean_dec(v_indName_1891_);
v___x_2037_ = lean_box(0);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v___x_2037_;
goto v___jp_1995_;
}
else
{
lean_object* v_toConstantVal_2038_; lean_object* v_numParams_2039_; lean_object* v_all_2040_; lean_object* v_numNested_2041_; lean_object* v_type_2042_; lean_object* v___x_2043_; 
v_toConstantVal_2038_ = lean_ctor_get(v_val_2035_, 0);
lean_inc_ref(v_toConstantVal_2038_);
v_numParams_2039_ = lean_ctor_get(v_val_2035_, 1);
lean_inc(v_numParams_2039_);
v_all_2040_ = lean_ctor_get(v_val_2035_, 3);
lean_inc(v_all_2040_);
v_numNested_2041_ = lean_ctor_get(v_val_2035_, 5);
lean_inc(v_numNested_2041_);
lean_dec_ref(v_val_2035_);
v_type_2042_ = lean_ctor_get(v_toConstantVal_2038_, 2);
lean_inc_ref(v_type_2042_);
lean_dec_ref(v_toConstantVal_2038_);
v___x_2043_ = l_Lean_Meta_isPropFormerType(v_type_2042_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; uint8_t v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
v___x_2045_ = lean_unbox(v_a_2044_);
lean_dec(v_a_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_inc_n(v_indName_1891_, 2);
v___x_2046_ = l_Lean_mkRecName(v_indName_1891_);
v___x_2047_ = l_Lean_mkBelowName(v_indName_1891_);
lean_inc(v___x_2047_);
lean_inc(v_numParams_2039_);
lean_inc(v___x_2046_);
v___x_2048_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2046_, v_numParams_2039_, v___x_2047_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
lean_dec_ref_known(v___x_2048_, 1);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = l_List_get_x21Internal___redArg(v___x_1901_, v_all_2040_, v___x_2049_);
lean_dec(v_all_2040_);
v___x_2051_ = lean_name_eq(v___x_2050_, v_indName_1891_);
lean_dec(v_indName_1891_);
lean_dec(v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
lean_dec(v___x_2047_);
lean_dec(v___x_2046_);
lean_dec(v_numNested_2041_);
lean_dec(v_numParams_2039_);
v___x_2052_ = lean_box(0);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v___x_2052_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2041_, v___x_2046_, v___x_2047_, v_numParams_2039_, v___x_2049_, v___x_2053_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_numNested_2041_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v___x_2053_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2055_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___y_2001_ = v_a_2029_;
v___y_2002_ = v___x_2032_;
v_a_2003_ = v_a_2055_;
goto v___jp_2000_;
}
}
}
else
{
lean_dec(v___x_2047_);
lean_dec(v___x_2046_);
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1891_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2048_, 1);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v_a_2056_;
goto v___jp_1995_;
}
else
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2048_, 1);
v___y_2001_ = v_a_2029_;
v___y_2002_ = v___x_2032_;
v_a_2003_ = v_a_2057_;
goto v___jp_2000_;
}
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1891_);
v___x_2058_ = lean_box(0);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v___x_2058_;
goto v___jp_1995_;
}
}
else
{
lean_object* v_a_2059_; 
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1891_);
v_a_2059_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2043_, 1);
v___y_2001_ = v_a_2029_;
v___y_2002_ = v___x_2032_;
v_a_2003_ = v_a_2059_;
goto v___jp_2000_;
}
}
}
else
{
lean_object* v___x_2060_; 
lean_dec(v_a_2034_);
lean_dec(v_indName_1891_);
v___x_2060_ = lean_box(0);
v___y_1996_ = v_a_2029_;
v___y_1997_ = v___x_2032_;
v_a_1998_ = v___x_2060_;
goto v___jp_1995_;
}
}
else
{
lean_object* v_a_2061_; 
lean_dec(v_indName_1891_);
v_a_2061_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2033_, 1);
v___y_2001_ = v_a_2029_;
v___y_2002_ = v___x_2032_;
v_a_2003_ = v_a_2061_;
goto v___jp_2000_;
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1891_);
v___x_2063_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
if (lean_obj_tag(v_a_2064_) == 5)
{
lean_object* v_val_2065_; uint8_t v_isRec_2066_; 
v_val_2065_ = lean_ctor_get(v_a_2064_, 0);
lean_inc_ref(v_val_2065_);
lean_dec_ref_known(v_a_2064_, 1);
v_isRec_2066_ = lean_ctor_get_uint8(v_val_2065_, sizeof(void*)*6);
if (v_isRec_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref(v_val_2065_);
lean_dec(v_indName_1891_);
v___x_2067_ = lean_box(0);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v___x_2067_;
goto v___jp_2017_;
}
else
{
lean_object* v_toConstantVal_2068_; lean_object* v_numParams_2069_; lean_object* v_all_2070_; lean_object* v_numNested_2071_; lean_object* v_type_2072_; lean_object* v___x_2073_; 
v_toConstantVal_2068_ = lean_ctor_get(v_val_2065_, 0);
lean_inc_ref(v_toConstantVal_2068_);
v_numParams_2069_ = lean_ctor_get(v_val_2065_, 1);
lean_inc(v_numParams_2069_);
v_all_2070_ = lean_ctor_get(v_val_2065_, 3);
lean_inc(v_all_2070_);
v_numNested_2071_ = lean_ctor_get(v_val_2065_, 5);
lean_inc(v_numNested_2071_);
lean_dec_ref(v_val_2065_);
v_type_2072_ = lean_ctor_get(v_toConstantVal_2068_, 2);
lean_inc_ref(v_type_2072_);
lean_dec_ref(v_toConstantVal_2068_);
v___x_2073_ = l_Lean_Meta_isPropFormerType(v_type_2072_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; uint8_t v___x_2075_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = lean_unbox(v_a_2074_);
lean_dec(v_a_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_inc_n(v_indName_1891_, 2);
v___x_2076_ = l_Lean_mkRecName(v_indName_1891_);
v___x_2077_ = l_Lean_mkBelowName(v_indName_1891_);
lean_inc(v___x_2077_);
lean_inc(v_numParams_2069_);
lean_inc(v___x_2076_);
v___x_2078_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2076_, v_numParams_2069_, v___x_2077_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
lean_dec_ref_known(v___x_2078_, 1);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = l_List_get_x21Internal___redArg(v___x_1901_, v_all_2070_, v___x_2079_);
lean_dec(v_all_2070_);
v___x_2081_ = lean_name_eq(v___x_2080_, v_indName_1891_);
lean_dec(v_indName_1891_);
lean_dec(v___x_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_dec(v___x_2077_);
lean_dec(v___x_2076_);
lean_dec(v_numNested_2071_);
lean_dec(v_numParams_2069_);
v___x_2082_ = lean_box(0);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v___x_2082_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_box(0);
v___x_2084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2071_, v___x_2076_, v___x_2077_, v_numParams_2069_, v___x_2079_, v___x_2083_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec(v_numNested_2071_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_dec_ref_known(v___x_2084_, 1);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v___x_2083_;
goto v___jp_2017_;
}
else
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___y_2023_ = v_a_2029_;
v___y_2024_ = v___x_2062_;
v_a_2025_ = v_a_2085_;
goto v___jp_2022_;
}
}
}
else
{
lean_dec(v___x_2077_);
lean_dec(v___x_2076_);
lean_dec(v_numNested_2071_);
lean_dec(v_all_2070_);
lean_dec(v_numParams_2069_);
lean_dec(v_indName_1891_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2078_, 1);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v_a_2086_;
goto v___jp_2017_;
}
else
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2078_, 1);
v___y_2023_ = v_a_2029_;
v___y_2024_ = v___x_2062_;
v_a_2025_ = v_a_2087_;
goto v___jp_2022_;
}
}
}
else
{
lean_object* v___x_2088_; 
lean_dec(v_numNested_2071_);
lean_dec(v_all_2070_);
lean_dec(v_numParams_2069_);
lean_dec(v_indName_1891_);
v___x_2088_ = lean_box(0);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v___x_2088_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_a_2089_; 
lean_dec(v_numNested_2071_);
lean_dec(v_all_2070_);
lean_dec(v_numParams_2069_);
lean_dec(v_indName_1891_);
v_a_2089_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2073_, 1);
v___y_2023_ = v_a_2029_;
v___y_2024_ = v___x_2062_;
v_a_2025_ = v_a_2089_;
goto v___jp_2022_;
}
}
}
else
{
lean_object* v___x_2090_; 
lean_dec(v_a_2064_);
lean_dec(v_indName_1891_);
v___x_2090_ = lean_box(0);
v___y_2018_ = v_a_2029_;
v___y_2019_ = v___x_2062_;
v_a_2020_ = v___x_2090_;
goto v___jp_2017_;
}
}
else
{
lean_object* v_a_2091_; 
lean_dec(v_indName_1891_);
v_a_2091_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2063_, 1);
v___y_2023_ = v_a_2029_;
v___y_2024_ = v___x_2062_;
v_a_2025_ = v_a_2091_;
goto v___jp_2022_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkBelow_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1891_ = stack[0].m_obj;
lean_object* v_a_1892_ = stack[1].m_obj;
lean_object* v_a_1893_ = stack[2].m_obj;
lean_object* v_a_1894_ = stack[3].m_obj;
lean_object* v_a_1895_ = stack[4].m_obj;
lean_object* v_res_2167_;
v_res_2167_ = l_Lean_mkBelow(v_indName_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
stack->m_obj
 = v_res_2167_;
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_mkBelow(v_indName_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
return v_res_2174_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v___x_2178_, lean_object* v_inst_2179_, lean_object* v_R_2180_, lean_object* v_a_2181_, lean_object* v_b_2182_, lean_object* v_c_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2175_, v___x_2176_, v___x_2177_, v___x_2178_, v_a_2181_, v_b_2182_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
return v___x_2189_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2175_ = stack[0].m_obj;
lean_object* v___x_2176_ = stack[1].m_obj;
lean_object* v___x_2177_ = stack[2].m_obj;
lean_object* v___x_2178_ = stack[3].m_obj;
lean_object* v_a_2181_ = stack[6].m_obj;
lean_object* v_b_2182_ = stack[7].m_obj;
lean_object* v___y_2184_ = stack[9].m_obj;
lean_object* v___y_2185_ = stack[10].m_obj;
lean_object* v___y_2186_ = stack[11].m_obj;
lean_object* v___y_2187_ = stack[12].m_obj;
lean_object* v_res_2190_;
v_res_2190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2175_, v___x_2176_, v___x_2177_, v___x_2178_, lean_box(0), lean_box(0), v_a_2181_, v_b_2182_, lean_box(0), v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
stack->m_obj
 = v_res_2190_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2191_, lean_object* v___x_2192_, lean_object* v___x_2193_, lean_object* v___x_2194_, lean_object* v_inst_2195_, lean_object* v_R_2196_, lean_object* v_a_2197_, lean_object* v_b_2198_, lean_object* v_c_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2191_, v___x_2192_, v___x_2193_, v___x_2194_, v_inst_2195_, v_R_2196_, v_a_2197_, v_b_2198_, v_c_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v_upperBound_2191_);
return v_res_2205_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2207_);
return v___x_2213_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2207_ = stack[1].m_obj;
lean_object* v___y_2208_ = stack[2].m_obj;
lean_object* v___y_2209_ = stack[3].m_obj;
lean_object* v___y_2210_ = stack[4].m_obj;
lean_object* v___y_2211_ = stack[5].m_obj;
lean_object* v_res_2214_;
v_res_2214_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_box(0), v_x_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
stack->m_obj
 = v_res_2214_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2215_, v_x_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
if (lean_obj_tag(v_a_2223_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = l_List_reverse___redArg(v_a_2224_);
return v___x_2225_;
}
else
{
lean_object* v_head_2226_; lean_object* v_tail_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2236_; 
v_head_2226_ = lean_ctor_get(v_a_2223_, 0);
v_tail_2227_ = lean_ctor_get(v_a_2223_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2223_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2229_ = v_a_2223_;
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_tail_2227_);
lean_inc(v_head_2226_);
lean_dec(v_a_2223_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_MessageData_ofExpr(v_head_2226_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_a_2224_);
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2224_);
v___x_2233_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
v_a_2223_ = v_tail_2227_;
v_a_2224_ = v___x_2233_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2237_, lean_object* v_v_2238_, lean_object* v_i_2239_){
_start:
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = lean_array_get_size(v_xs_2237_);
v___x_2241_ = lean_nat_dec_lt(v_i_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_i_2239_);
v___x_2242_ = lean_box(0);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; uint8_t v___x_2244_; 
v___x_2243_ = lean_array_fget_borrowed(v_xs_2237_, v_i_2239_);
v___x_2244_ = lean_expr_eqv(v___x_2243_, v_v_2238_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_add(v_i_2239_, v___x_2245_);
lean_dec(v_i_2239_);
v_i_2239_ = v___x_2246_;
goto _start;
}
else
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_i_2239_);
return v___x_2248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2249_, lean_object* v_v_2250_, lean_object* v_i_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2249_, v_v_2250_, v_i_2251_);
lean_dec_ref(v_v_2250_);
lean_dec_ref(v_xs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2253_, lean_object* v_v_2254_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2253_, v_v_2254_, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2257_, lean_object* v_v_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2257_, v_v_2258_);
lean_dec_ref(v_v_2258_);
lean_dec_ref(v_xs_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2260_, lean_object* v_v_2261_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2260_, v_v_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = lean_box(0);
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
v_val_2264_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2262_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v___x_2262_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_val_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2272_, lean_object* v_v_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2272_, v_v_2273_);
lean_dec_ref(v_v_2273_);
lean_dec_ref(v_xs_2272_);
return v_res_2274_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2277_ = l_Lean_stringToMessageData(v___x_2276_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2279_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
return v___x_2280_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2281_, lean_object* v_prods_2282_, lean_object* v_motives_2283_, lean_object* v_fs_2284_, lean_object* v_minor__type_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
if (lean_obj_tag(v_x_2286_) == 5)
{
lean_object* v_fn_2294_; lean_object* v_arg_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v_fn_2294_ = lean_ctor_get(v_x_2286_, 0);
lean_inc_ref(v_fn_2294_);
v_arg_2295_ = lean_ctor_get(v_x_2286_, 1);
lean_inc_ref(v_arg_2295_);
lean_dec_ref_known(v_x_2286_, 2);
v___x_2296_ = lean_array_set(v_x_2287_, v_x_2288_, v_arg_2295_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_sub(v_x_2288_, v___x_2297_);
lean_dec(v_x_2288_);
v_x_2286_ = v_fn_2294_;
v_x_2287_ = v___x_2296_;
v_x_2288_ = v___x_2298_;
goto _start;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v_x_2288_);
v___x_2300_ = l_Lean_instInhabitedExpr;
v___x_2301_ = l_Lean_Meta_PProdN_mk(v_rlvl_2281_, v_prods_2282_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v___x_2303_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2283_, v_x_2286_);
lean_dec_ref(v_x_2286_);
if (lean_obj_tag(v___x_2303_) == 1)
{
lean_object* v_val_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec_ref(v_minor__type_2285_);
lean_dec_ref(v_motives_2283_);
v_val_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_val_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = lean_array_get_borrowed(v___x_2300_, v_fs_2284_, v_val_2304_);
lean_dec(v_val_2304_);
lean_inc(v_a_2302_);
v___x_2306_ = lean_array_push(v_x_2287_, v_a_2302_);
lean_inc(v___x_2305_);
v___x_2307_ = l_Lean_mkAppN(v___x_2305_, v___x_2306_);
lean_dec_ref(v___x_2306_);
v___x_2308_ = l_Lean_Meta_mkPProdMk(v___x_2307_, v_a_2302_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec(v___x_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_x_2287_);
v___x_2309_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2310_ = l_Lean_MessageData_ofExpr(v_minor__type_2285_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_array_to_list(v_motives_2283_);
v___x_2315_ = lean_box(0);
v___x_2316_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2314_, v___x_2315_);
v___x_2317_ = l_Lean_MessageData_ofList(v___x_2316_);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2313_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2318_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2319_;
}
}
else
{
lean_dec_ref(v_x_2287_);
lean_dec_ref(v_x_2286_);
lean_dec_ref(v_minor__type_2285_);
lean_dec_ref(v_motives_2283_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_2281_ = stack[0].m_obj;
lean_object* v_prods_2282_ = stack[1].m_obj;
lean_object* v_motives_2283_ = stack[2].m_obj;
lean_object* v_fs_2284_ = stack[3].m_obj;
lean_object* v_minor__type_2285_ = stack[4].m_obj;
lean_object* v_x_2286_ = stack[5].m_obj;
lean_object* v_x_2287_ = stack[6].m_obj;
lean_object* v_x_2288_ = stack[7].m_obj;
lean_object* v___y_2289_ = stack[8].m_obj;
lean_object* v___y_2290_ = stack[9].m_obj;
lean_object* v___y_2291_ = stack[10].m_obj;
lean_object* v___y_2292_ = stack[11].m_obj;
lean_object* v_res_2320_;
v_res_2320_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2281_, v_prods_2282_, v_motives_2283_, v_fs_2284_, v_minor__type_2285_, v_x_2286_, v_x_2287_, v_x_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
stack->m_obj
 = v_res_2320_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2321_, lean_object* v_prods_2322_, lean_object* v_motives_2323_, lean_object* v_fs_2324_, lean_object* v_minor__type_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2321_, v_prods_2322_, v_motives_2323_, v_fs_2324_, v_minor__type_2325_, v_x_2326_, v_x_2327_, v_x_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_fs_2324_);
return v_res_2334_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2335_; lean_object* v_dummy_2336_; 
v___x_2335_ = lean_box(0);
v_dummy_2336_ = l_Lean_Expr_sort___override(v___x_2335_);
return v_dummy_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2337_, lean_object* v_head_2338_, lean_object* v_belows_2339_, lean_object* v_prods_2340_, lean_object* v_rlvl_2341_, lean_object* v_fs_2342_, lean_object* v_minor__type_2343_, lean_object* v_tail_2344_, lean_object* v_arg__args_2345_, lean_object* v_arg__type_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2337_, v_head_2338_, v_belows_2339_, v_prods_2340_, v_rlvl_2341_, v_fs_2342_, v_minor__type_2343_, v_tail_2344_, v_arg__args_2345_, v_arg__type_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_arg__args_2345_);
return v_res_2352_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2353_, lean_object* v_motives_2354_, lean_object* v_belows_2355_, lean_object* v_fs_2356_, lean_object* v_minor__type_2357_, lean_object* v_prods_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
if (lean_obj_tag(v_a_2359_) == 0)
{
lean_object* v_dummy_2365_; lean_object* v_nargs_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref(v_belows_2355_);
v_dummy_2365_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2366_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2357_);
lean_inc(v_nargs_2366_);
v___x_2367_ = lean_mk_array(v_nargs_2366_, v_dummy_2365_);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_sub(v_nargs_2366_, v___x_2368_);
lean_dec(v_nargs_2366_);
lean_inc_ref(v_minor__type_2357_);
v___x_2370_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2353_, v_prods_2358_, v_motives_2354_, v_fs_2356_, v_minor__type_2357_, v_minor__type_2357_, v___x_2367_, v___x_2369_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
lean_dec_ref(v_fs_2356_);
return v___x_2370_;
}
else
{
lean_object* v_head_2371_; lean_object* v_tail_2372_; lean_object* v___f_2373_; lean_object* v___x_2374_; 
v_head_2371_ = lean_ctor_get(v_a_2359_, 0);
lean_inc_n(v_head_2371_, 2);
v_tail_2372_ = lean_ctor_get(v_a_2359_, 1);
lean_inc(v_tail_2372_);
lean_dec_ref_known(v_a_2359_, 2);
v___f_2373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2373_, 0, v_motives_2354_);
lean_closure_set(v___f_2373_, 1, v_head_2371_);
lean_closure_set(v___f_2373_, 2, v_belows_2355_);
lean_closure_set(v___f_2373_, 3, v_prods_2358_);
lean_closure_set(v___f_2373_, 4, v_rlvl_2353_);
lean_closure_set(v___f_2373_, 5, v_fs_2356_);
lean_closure_set(v___f_2373_, 6, v_minor__type_2357_);
lean_closure_set(v___f_2373_, 7, v_tail_2372_);
lean_inc(v_a_2363_);
lean_inc_ref(v_a_2362_);
lean_inc(v_a_2361_);
lean_inc_ref(v_a_2360_);
v___x_2374_ = lean_infer_type(v_head_2371_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = 0;
v___x_2377_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2375_, v___f_2373_, v___x_2376_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
return v___x_2377_;
}
else
{
lean_dec_ref(v___f_2373_);
return v___x_2374_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_2353_ = stack[0].m_obj;
lean_object* v_motives_2354_ = stack[1].m_obj;
lean_object* v_belows_2355_ = stack[2].m_obj;
lean_object* v_fs_2356_ = stack[3].m_obj;
lean_object* v_minor__type_2357_ = stack[4].m_obj;
lean_object* v_prods_2358_ = stack[5].m_obj;
lean_object* v_a_2359_ = stack[6].m_obj;
lean_object* v_a_2360_ = stack[7].m_obj;
lean_object* v_a_2361_ = stack[8].m_obj;
lean_object* v_a_2362_ = stack[9].m_obj;
lean_object* v_a_2363_ = stack[10].m_obj;
lean_object* v_res_2378_;
v_res_2378_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2353_, v_motives_2354_, v_belows_2355_, v_fs_2356_, v_minor__type_2357_, v_prods_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
stack->m_obj
 = v_res_2378_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2379_, lean_object* v_rlvl_2380_, lean_object* v_motives_2381_, lean_object* v_belows_2382_, lean_object* v_fs_2383_, lean_object* v_minor__type_2384_, lean_object* v_tail_2385_, uint8_t v___x_2386_, uint8_t v___x_2387_, uint8_t v___x_2388_, lean_object* v_arg_x27_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_inc_ref(v_arg_x27_2389_);
v___x_2395_ = lean_array_push(v_prods_2379_, v_arg_x27_2389_);
v___x_2396_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2380_, v_motives_2381_, v_belows_2382_, v_fs_2383_, v_minor__type_2384_, v___x_2395_, v_tail_2385_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_mk_empty_array_with_capacity(v___x_2398_);
v___x_2400_ = lean_array_push(v___x_2399_, v_arg_x27_2389_);
v___x_2401_ = l_Lean_Meta_mkLambdaFVars(v___x_2400_, v_a_2397_, v___x_2386_, v___x_2387_, v___x_2386_, v___x_2387_, v___x_2388_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec_ref(v___x_2400_);
return v___x_2401_;
}
else
{
lean_dec_ref(v_arg_x27_2389_);
return v___x_2396_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_prods_2379_ = stack[0].m_obj;
lean_object* v_rlvl_2380_ = stack[1].m_obj;
lean_object* v_motives_2381_ = stack[2].m_obj;
lean_object* v_belows_2382_ = stack[3].m_obj;
lean_object* v_fs_2383_ = stack[4].m_obj;
lean_object* v_minor__type_2384_ = stack[5].m_obj;
lean_object* v_tail_2385_ = stack[6].m_obj;
uint8_t v___x_2386_ = stack[7].m_num;
uint8_t v___x_2387_ = stack[8].m_num;
uint8_t v___x_2388_ = stack[9].m_num;
lean_object* v_arg_x27_2389_ = stack[10].m_obj;
lean_object* v___y_2390_ = stack[11].m_obj;
lean_object* v___y_2391_ = stack[12].m_obj;
lean_object* v___y_2392_ = stack[13].m_obj;
lean_object* v___y_2393_ = stack[14].m_obj;
lean_object* v_res_2402_;
v_res_2402_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2379_, v_rlvl_2380_, v_motives_2381_, v_belows_2382_, v_fs_2383_, v_minor__type_2384_, v_tail_2385_, v___x_2386_, v___x_2387_, v___x_2388_, v_arg_x27_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
stack->m_obj
 = v_res_2402_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2403_, lean_object* v_rlvl_2404_, lean_object* v_motives_2405_, lean_object* v_belows_2406_, lean_object* v_fs_2407_, lean_object* v_minor__type_2408_, lean_object* v_tail_2409_, lean_object* v___x_2410_, lean_object* v___x_2411_, lean_object* v___x_2412_, lean_object* v_arg_x27_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v___x_1772__boxed_2419_; uint8_t v___x_1773__boxed_2420_; uint8_t v___x_1774__boxed_2421_; lean_object* v_res_2422_; 
v___x_1772__boxed_2419_ = lean_unbox(v___x_2410_);
v___x_1773__boxed_2420_ = lean_unbox(v___x_2411_);
v___x_1774__boxed_2421_ = lean_unbox(v___x_2412_);
v_res_2422_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2403_, v_rlvl_2404_, v_motives_2405_, v_belows_2406_, v_fs_2407_, v_minor__type_2408_, v_tail_2409_, v___x_1772__boxed_2419_, v___x_1773__boxed_2420_, v___x_1774__boxed_2421_, v_arg_x27_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2422_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2423_, lean_object* v_head_2424_, lean_object* v_belows_2425_, lean_object* v_arg__type_2426_, lean_object* v_prods_2427_, lean_object* v_rlvl_2428_, lean_object* v_fs_2429_, lean_object* v_minor__type_2430_, lean_object* v_tail_2431_, lean_object* v_arg__args_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
if (lean_obj_tag(v_x_2433_) == 5)
{
lean_object* v_fn_2441_; lean_object* v_arg_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_fn_2441_ = lean_ctor_get(v_x_2433_, 0);
lean_inc_ref(v_fn_2441_);
v_arg_2442_ = lean_ctor_get(v_x_2433_, 1);
lean_inc_ref(v_arg_2442_);
lean_dec_ref_known(v_x_2433_, 2);
v___x_2443_ = lean_array_set(v_x_2434_, v_x_2435_, v_arg_2442_);
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_sub(v_x_2435_, v___x_2444_);
lean_dec(v_x_2435_);
v_x_2433_ = v_fn_2441_;
v_x_2434_ = v___x_2443_;
v_x_2435_ = v___x_2445_;
goto _start;
}
else
{
lean_object* v___x_2447_; 
lean_dec(v_x_2435_);
v___x_2447_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2423_, v_x_2433_);
lean_dec_ref(v_x_2433_);
if (lean_obj_tag(v___x_2447_) == 1)
{
lean_object* v_val_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = l_Lean_instInhabitedExpr;
v___x_2450_ = l_Lean_Expr_fvarId_x21(v_head_2424_);
lean_dec_ref(v_head_2424_);
v___x_2451_ = l_Lean_FVarId_getUserName___redArg(v___x_2450_, v___y_2436_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = lean_array_get_borrowed(v___x_2449_, v_belows_2425_, v_val_2448_);
lean_dec(v_val_2448_);
lean_inc(v___x_2453_);
v___x_2454_ = l_Lean_mkAppN(v___x_2453_, v_x_2434_);
lean_dec_ref(v_x_2434_);
v___x_2455_ = l_Lean_Meta_mkPProd(v_arg__type_2426_, v___x_2454_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; uint8_t v___x_2457_; uint8_t v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = 0;
v___x_2458_ = 1;
v___x_2459_ = 1;
v___x_2460_ = lean_box(v___x_2457_);
v___x_2461_ = lean_box(v___x_2458_);
v___x_2462_ = lean_box(v___x_2459_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2463_, 0, v_prods_2427_);
lean_closure_set(v___f_2463_, 1, v_rlvl_2428_);
lean_closure_set(v___f_2463_, 2, v_motives_2423_);
lean_closure_set(v___f_2463_, 3, v_belows_2425_);
lean_closure_set(v___f_2463_, 4, v_fs_2429_);
lean_closure_set(v___f_2463_, 5, v_minor__type_2430_);
lean_closure_set(v___f_2463_, 6, v_tail_2431_);
lean_closure_set(v___f_2463_, 7, v___x_2460_);
lean_closure_set(v___f_2463_, 8, v___x_2461_);
lean_closure_set(v___f_2463_, 9, v___x_2462_);
v___x_2464_ = l_Lean_Meta_mkForallFVars(v_arg__args_2432_, v_a_2456_, v___x_2457_, v___x_2458_, v___x_2458_, v___x_2459_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; lean_object* v___x_2466_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
v___x_2466_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2452_, v_a_2465_, v___f_2463_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2466_;
}
else
{
lean_dec_ref(v___f_2463_);
lean_dec(v_a_2452_);
return v___x_2464_;
}
}
else
{
lean_dec(v_a_2452_);
lean_dec(v_tail_2431_);
lean_dec_ref(v_minor__type_2430_);
lean_dec_ref(v_fs_2429_);
lean_dec(v_rlvl_2428_);
lean_dec_ref(v_prods_2427_);
lean_dec_ref(v_belows_2425_);
lean_dec_ref(v_motives_2423_);
return v___x_2455_;
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_val_2448_);
lean_dec_ref(v_x_2434_);
lean_dec(v_tail_2431_);
lean_dec_ref(v_minor__type_2430_);
lean_dec_ref(v_fs_2429_);
lean_dec(v_rlvl_2428_);
lean_dec_ref(v_prods_2427_);
lean_dec_ref(v_arg__type_2426_);
lean_dec_ref(v_belows_2425_);
lean_dec_ref(v_motives_2423_);
v_a_2467_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2451_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2451_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v___x_2475_; 
lean_dec(v___x_2447_);
lean_dec_ref(v_x_2434_);
lean_dec_ref(v_arg__type_2426_);
v___x_2475_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2428_, v_motives_2423_, v_belows_2425_, v_fs_2429_, v_minor__type_2430_, v_prods_2427_, v_tail_2431_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v_a_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; uint8_t v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; 
v_a_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_a_2476_);
lean_dec_ref_known(v___x_2475_, 1);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_mk_empty_array_with_capacity(v___x_2477_);
v___x_2479_ = lean_array_push(v___x_2478_, v_head_2424_);
v___x_2480_ = 0;
v___x_2481_ = 1;
v___x_2482_ = 1;
v___x_2483_ = l_Lean_Meta_mkLambdaFVars(v___x_2479_, v_a_2476_, v___x_2480_, v___x_2481_, v___x_2480_, v___x_2481_, v___x_2482_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec_ref(v___x_2479_);
return v___x_2483_;
}
else
{
lean_dec_ref(v_head_2424_);
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_motives_2423_ = stack[0].m_obj;
lean_object* v_head_2424_ = stack[1].m_obj;
lean_object* v_belows_2425_ = stack[2].m_obj;
lean_object* v_arg__type_2426_ = stack[3].m_obj;
lean_object* v_prods_2427_ = stack[4].m_obj;
lean_object* v_rlvl_2428_ = stack[5].m_obj;
lean_object* v_fs_2429_ = stack[6].m_obj;
lean_object* v_minor__type_2430_ = stack[7].m_obj;
lean_object* v_tail_2431_ = stack[8].m_obj;
lean_object* v_arg__args_2432_ = stack[9].m_obj;
lean_object* v_x_2433_ = stack[10].m_obj;
lean_object* v_x_2434_ = stack[11].m_obj;
lean_object* v_x_2435_ = stack[12].m_obj;
lean_object* v___y_2436_ = stack[13].m_obj;
lean_object* v___y_2437_ = stack[14].m_obj;
lean_object* v___y_2438_ = stack[15].m_obj;
lean_object* v___y_2439_ = stack[16].m_obj;
lean_object* v_res_2484_;
v_res_2484_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2423_, v_head_2424_, v_belows_2425_, v_arg__type_2426_, v_prods_2427_, v_rlvl_2428_, v_fs_2429_, v_minor__type_2430_, v_tail_2431_, v_arg__args_2432_, v_x_2433_, v_x_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
stack->m_obj
 = v_res_2484_;
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2485_, lean_object* v_head_2486_, lean_object* v_belows_2487_, lean_object* v_prods_2488_, lean_object* v_rlvl_2489_, lean_object* v_fs_2490_, lean_object* v_minor__type_2491_, lean_object* v_tail_2492_, lean_object* v_arg__args_2493_, lean_object* v_arg__type_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_dummy_2500_; lean_object* v_nargs_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_dummy_2500_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2501_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2494_);
lean_inc(v_nargs_2501_);
v___x_2502_ = lean_mk_array(v_nargs_2501_, v_dummy_2500_);
v___x_2503_ = lean_unsigned_to_nat(1u);
v___x_2504_ = lean_nat_sub(v_nargs_2501_, v___x_2503_);
lean_dec(v_nargs_2501_);
lean_inc_ref(v_arg__type_2494_);
v___x_2505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2485_, v_head_2486_, v_belows_2487_, v_arg__type_2494_, v_prods_2488_, v_rlvl_2489_, v_fs_2490_, v_minor__type_2491_, v_tail_2492_, v_arg__args_2493_, v_arg__type_2494_, v___x_2502_, v___x_2504_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2505_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motives_2485_ = stack[0].m_obj;
lean_object* v_head_2486_ = stack[1].m_obj;
lean_object* v_belows_2487_ = stack[2].m_obj;
lean_object* v_prods_2488_ = stack[3].m_obj;
lean_object* v_rlvl_2489_ = stack[4].m_obj;
lean_object* v_fs_2490_ = stack[5].m_obj;
lean_object* v_minor__type_2491_ = stack[6].m_obj;
lean_object* v_tail_2492_ = stack[7].m_obj;
lean_object* v_arg__args_2493_ = stack[8].m_obj;
lean_object* v_arg__type_2494_ = stack[9].m_obj;
lean_object* v___y_2495_ = stack[10].m_obj;
lean_object* v___y_2496_ = stack[11].m_obj;
lean_object* v___y_2497_ = stack[12].m_obj;
lean_object* v___y_2498_ = stack[13].m_obj;
lean_object* v_res_2506_;
v_res_2506_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2485_, v_head_2486_, v_belows_2487_, v_prods_2488_, v_rlvl_2489_, v_fs_2490_, v_minor__type_2491_, v_tail_2492_, v_arg__args_2493_, v_arg__type_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
stack->m_obj
 = v_res_2506_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2507_, lean_object* v_motives_2508_, lean_object* v_belows_2509_, lean_object* v_fs_2510_, lean_object* v_minor__type_2511_, lean_object* v_prods_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2507_, v_motives_2508_, v_belows_2509_, v_fs_2510_, v_minor__type_2511_, v_prods_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2520_ = _args[0];
lean_object* v_head_2521_ = _args[1];
lean_object* v_belows_2522_ = _args[2];
lean_object* v_arg__type_2523_ = _args[3];
lean_object* v_prods_2524_ = _args[4];
lean_object* v_rlvl_2525_ = _args[5];
lean_object* v_fs_2526_ = _args[6];
lean_object* v_minor__type_2527_ = _args[7];
lean_object* v_tail_2528_ = _args[8];
lean_object* v_arg__args_2529_ = _args[9];
lean_object* v_x_2530_ = _args[10];
lean_object* v_x_2531_ = _args[11];
lean_object* v_x_2532_ = _args[12];
lean_object* v___y_2533_ = _args[13];
lean_object* v___y_2534_ = _args[14];
lean_object* v___y_2535_ = _args[15];
lean_object* v___y_2536_ = _args[16];
lean_object* v___y_2537_ = _args[17];
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2520_, v_head_2521_, v_belows_2522_, v_arg__type_2523_, v_prods_2524_, v_rlvl_2525_, v_fs_2526_, v_minor__type_2527_, v_tail_2528_, v_arg__args_2529_, v_x_2530_, v_x_2531_, v_x_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec_ref(v_arg__args_2529_);
return v_res_2538_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2539_, lean_object* v_motives_2540_, lean_object* v_belows_2541_, lean_object* v_fs_2542_, lean_object* v_minor__args_2543_, lean_object* v_minor__type_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2551_ = lean_array_to_list(v_minor__args_2543_);
v___x_2552_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2539_, v_motives_2540_, v_belows_2541_, v_fs_2542_, v_minor__type_2544_, v___x_2550_, v___x_2551_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2552_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_2539_ = stack[0].m_obj;
lean_object* v_motives_2540_ = stack[1].m_obj;
lean_object* v_belows_2541_ = stack[2].m_obj;
lean_object* v_fs_2542_ = stack[3].m_obj;
lean_object* v_minor__args_2543_ = stack[4].m_obj;
lean_object* v_minor__type_2544_ = stack[5].m_obj;
lean_object* v___y_2545_ = stack[6].m_obj;
lean_object* v___y_2546_ = stack[7].m_obj;
lean_object* v___y_2547_ = stack[8].m_obj;
lean_object* v___y_2548_ = stack[9].m_obj;
lean_object* v_res_2553_;
v_res_2553_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2539_, v_motives_2540_, v_belows_2541_, v_fs_2542_, v_minor__args_2543_, v_minor__type_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2554_, lean_object* v_motives_2555_, lean_object* v_belows_2556_, lean_object* v_fs_2557_, lean_object* v_minor__args_2558_, lean_object* v_minor__type_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2554_, v_motives_2555_, v_belows_2556_, v_fs_2557_, v_minor__args_2558_, v_minor__type_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2565_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2566_, lean_object* v_motives_2567_, lean_object* v_belows_2568_, lean_object* v_fs_2569_, lean_object* v_minorType_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___f_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___f_2576_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2576_, 0, v_rlvl_2566_);
lean_closure_set(v___f_2576_, 1, v_motives_2567_);
lean_closure_set(v___f_2576_, 2, v_belows_2568_);
lean_closure_set(v___f_2576_, 3, v_fs_2569_);
v___x_2577_ = 0;
v___x_2578_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2570_, v___f_2576_, v___x_2577_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
return v___x_2578_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_0interp(lean_interpreter_value* stack)
{
lean_object* v_rlvl_2566_ = stack[0].m_obj;
lean_object* v_motives_2567_ = stack[1].m_obj;
lean_object* v_belows_2568_ = stack[2].m_obj;
lean_object* v_fs_2569_ = stack[3].m_obj;
lean_object* v_minorType_2570_ = stack[4].m_obj;
lean_object* v_a_2571_ = stack[5].m_obj;
lean_object* v_a_2572_ = stack[6].m_obj;
lean_object* v_a_2573_ = stack[7].m_obj;
lean_object* v_a_2574_ = stack[8].m_obj;
lean_object* v_res_2579_;
v_res_2579_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2566_, v_motives_2567_, v_belows_2568_, v_fs_2569_, v_minorType_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
stack->m_obj
 = v_res_2579_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2580_, lean_object* v_motives_2581_, lean_object* v_belows_2582_, lean_object* v_fs_2583_, lean_object* v_minorType_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2580_, v_motives_2581_, v_belows_2582_, v_fs_2583_, v_minorType_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
return v_res_2590_;
}
}
lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___f_2597_; lean_object* v___x_27356__overap_2598_; lean_object* v___x_2599_; 
v___f_2597_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27356__overap_2598_ = lean_panic_fn_borrowed(v___f_2597_, v_msg_2591_);
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
v___x_2599_ = lean_apply_5(v___x_27356__overap_2598_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, lean_box(0));
return v___x_2599_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2591_ = stack[0].m_obj;
lean_object* v___y_2592_ = stack[1].m_obj;
lean_object* v___y_2593_ = stack[2].m_obj;
lean_object* v___y_2594_ = stack[3].m_obj;
lean_object* v___y_2595_ = stack[4].m_obj;
lean_object* v_res_2600_;
v_res_2600_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
stack->m_obj
 = v_res_2600_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
return v_res_2607_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2608_, lean_object* v___y_2609_){
_start:
{
uint8_t v___x_2611_; 
v___x_2611_ = l_Lean_Expr_hasMVar(v_e_2608_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v_e_2608_);
return v___x_2612_;
}
else
{
lean_object* v___x_2613_; lean_object* v_mctx_2614_; lean_object* v___x_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2618_; lean_object* v_cache_2619_; lean_object* v_zetaDeltaFVarIds_2620_; lean_object* v_postponed_2621_; lean_object* v_diag_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2631_; 
v___x_2613_ = lean_st_ref_get(v___y_2609_);
v_mctx_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_ref(v_mctx_2614_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Lean_instantiateMVarsCore(v_mctx_2614_, v_e_2608_);
v_fst_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_fst_2616_);
v_snd_2617_ = lean_ctor_get(v___x_2615_, 1);
lean_inc(v_snd_2617_);
lean_dec_ref(v___x_2615_);
v___x_2618_ = lean_st_ref_take(v___y_2609_);
v_cache_2619_ = lean_ctor_get(v___x_2618_, 1);
v_zetaDeltaFVarIds_2620_ = lean_ctor_get(v___x_2618_, 2);
v_postponed_2621_ = lean_ctor_get(v___x_2618_, 3);
v_diag_2622_ = lean_ctor_get(v___x_2618_, 4);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2631_ == 0)
{
lean_object* v_unused_2632_; 
v_unused_2632_ = lean_ctor_get(v___x_2618_, 0);
lean_dec(v_unused_2632_);
v___x_2624_ = v___x_2618_;
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_diag_2622_);
lean_inc(v_postponed_2621_);
lean_inc(v_zetaDeltaFVarIds_2620_);
lean_inc(v_cache_2619_);
lean_dec(v___x_2618_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2631_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v_snd_2617_);
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_snd_2617_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_cache_2619_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v_zetaDeltaFVarIds_2620_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v_postponed_2621_);
lean_ctor_set(v_reuseFailAlloc_2630_, 4, v_diag_2622_);
v___x_2627_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = lean_st_ref_put(v___y_2609_, v___x_2627_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_fst_2616_);
return v___x_2629_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2608_ = stack[0].m_obj;
lean_object* v___y_2609_ = stack[1].m_obj;
lean_object* v_res_2633_;
v_res_2633_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2608_, v___y_2609_);
stack->m_obj
 = v_res_2633_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2634_, v___y_2635_);
lean_dec(v___y_2635_);
return v_res_2637_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2638_, v___y_2640_);
return v___x_2644_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2638_ = stack[0].m_obj;
lean_object* v___y_2639_ = stack[1].m_obj;
lean_object* v___y_2640_ = stack[2].m_obj;
lean_object* v___y_2641_ = stack[3].m_obj;
lean_object* v___y_2642_ = stack[4].m_obj;
lean_object* v_res_2645_;
v_res_2645_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
stack->m_obj
 = v_res_2645_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
return v_res_2652_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v_env_2657_; lean_object* v_toConstantVal_2658_; lean_object* v_value_2659_; lean_object* v_all_2660_; uint8_t v___y_2662_; lean_object* v_type_2670_; uint8_t v___x_2671_; 
v___x_2656_ = lean_st_ref_get(v___y_2654_);
v_env_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_ref_n(v_env_2657_, 2);
lean_dec(v___x_2656_);
v_toConstantVal_2658_ = lean_ctor_get(v_thm_2653_, 0);
v_value_2659_ = lean_ctor_get(v_thm_2653_, 1);
v_all_2660_ = lean_ctor_get(v_thm_2653_, 2);
v_type_2670_ = lean_ctor_get(v_toConstantVal_2658_, 2);
v___x_2671_ = l_Lean_Environment_hasUnsafe(v_env_2657_, v_type_2670_);
if (v___x_2671_ == 0)
{
uint8_t v___x_2672_; 
v___x_2672_ = l_Lean_Environment_hasUnsafe(v_env_2657_, v_value_2659_);
v___y_2662_ = v___x_2672_;
goto v___jp_2661_;
}
else
{
lean_dec_ref(v_env_2657_);
v___y_2662_ = v___x_2671_;
goto v___jp_2661_;
}
v___jp_2661_:
{
if (v___y_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_thm_2653_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_inc(v_all_2660_);
lean_inc_ref(v_value_2659_);
lean_inc_ref(v_toConstantVal_2658_);
lean_dec_ref(v_thm_2653_);
v___x_2665_ = lean_box(0);
v___x_2666_ = 0;
v___x_2667_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2667_, 0, v_toConstantVal_2658_);
lean_ctor_set(v___x_2667_, 1, v_value_2659_);
lean_ctor_set(v___x_2667_, 2, v___x_2665_);
lean_ctor_set(v___x_2667_, 3, v_all_2660_);
lean_ctor_set_uint8(v___x_2667_, sizeof(void*)*4, v___x_2666_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_2653_ = stack[0].m_obj;
lean_object* v___y_2654_ = stack[1].m_obj;
lean_object* v_res_2673_;
v_res_2673_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2653_, v___y_2654_);
stack->m_obj
 = v_res_2673_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2674_, v___y_2675_);
lean_dec(v___y_2675_);
return v_res_2677_;
}
}
lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2678_, v___y_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT void l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_2678_ = stack[0].m_obj;
lean_object* v___y_2679_ = stack[1].m_obj;
lean_object* v___y_2680_ = stack[2].m_obj;
lean_object* v___y_2681_ = stack[3].m_obj;
lean_object* v___y_2682_ = stack[4].m_obj;
lean_object* v_res_2685_;
v_res_2685_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
stack->m_obj
 = v_res_2685_;
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_all_2697_, lean_object* v___x_2698_, lean_object* v___x_2699_, lean_object* v___x_2700_, lean_object* v_x_2701_){
_start:
{
lean_object* v___y_2703_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = lean_array_get_size(v_all_2697_);
v___x_2708_ = lean_nat_dec_lt(v_x_2701_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2709_ = lean_array_get_borrowed(v___x_2698_, v_all_2697_, v___x_2699_);
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2711_ = lean_nat_sub(v_x_2701_, v___x_2707_);
v___x_2712_ = lean_nat_add(v___x_2711_, v___x_2700_);
lean_dec(v___x_2711_);
v___x_2713_ = l_Nat_reprFast(v___x_2712_);
v___x_2714_ = lean_string_append(v___x_2710_, v___x_2713_);
lean_dec_ref(v___x_2713_);
lean_inc(v___x_2709_);
v___x_2715_ = l_Lean_Name_str___override(v___x_2709_, v___x_2714_);
v___y_2703_ = v___x_2715_;
goto v___jp_2702_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2716_ = lean_array_fget_borrowed(v_all_2697_, v_x_2701_);
lean_inc(v___x_2716_);
v___x_2717_ = l_Lean_mkBelowName(v___x_2716_);
v___y_2703_ = v___x_2717_;
goto v___jp_2702_;
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = l_Lean_Expr_const___override(v___y_2703_, v___x_2694_);
v___x_2705_ = l_Array_append___redArg(v___x_2695_, v___x_2696_);
v___x_2706_ = l_Lean_mkAppN(v___x_2704_, v___x_2705_);
lean_dec_ref(v___x_2705_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2718_, lean_object* v___x_2719_, lean_object* v___x_2720_, lean_object* v_all_2721_, lean_object* v___x_2722_, lean_object* v___x_2723_, lean_object* v___x_2724_, lean_object* v_x_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2718_, v___x_2719_, v___x_2720_, v_all_2721_, v___x_2722_, v___x_2723_, v___x_2724_, v_x_2725_);
lean_dec(v_x_2725_);
lean_dec(v___x_2724_);
lean_dec(v___x_2723_);
lean_dec(v___x_2722_);
lean_dec_ref(v_all_2721_);
lean_dec_ref(v___x_2720_);
return v_res_2726_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2727_, lean_object* v___x_2728_, lean_object* v___x_2729_, lean_object* v_fs_2730_, lean_object* v_as_2731_, size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_usize_dec_lt(v_i_2733_, v_sz_2732_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec_ref(v_fs_2730_);
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2728_);
lean_dec(v___x_2727_);
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_b_2734_);
return v___x_2741_;
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2743_; 
v_a_2742_ = lean_array_uget_borrowed(v_as_2731_, v_i_2733_);
lean_inc(v___y_2738_);
lean_inc_ref(v___y_2737_);
lean_inc(v___y_2736_);
lean_inc_ref(v___y_2735_);
lean_inc(v_a_2742_);
v___x_2743_ = lean_infer_type(v_a_2742_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
lean_inc_ref(v_fs_2730_);
lean_inc_ref(v___x_2729_);
lean_inc_ref(v___x_2728_);
lean_inc(v___x_2727_);
v___x_2745_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2727_, v___x_2728_, v___x_2729_, v_fs_2730_, v_a_2744_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = l_Lean_Expr_app___override(v_b_2734_, v_a_2746_);
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_add(v_i_2733_, v___x_2748_);
v_i_2733_ = v___x_2749_;
v_b_2734_ = v___x_2747_;
goto _start;
}
else
{
lean_dec_ref(v_b_2734_);
lean_dec_ref(v_fs_2730_);
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2728_);
lean_dec(v___x_2727_);
return v___x_2745_;
}
}
else
{
lean_dec_ref(v_b_2734_);
lean_dec_ref(v_fs_2730_);
lean_dec_ref(v___x_2729_);
lean_dec_ref(v___x_2728_);
lean_dec(v___x_2727_);
return v___x_2743_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2727_ = stack[0].m_obj;
lean_object* v___x_2728_ = stack[1].m_obj;
lean_object* v___x_2729_ = stack[2].m_obj;
lean_object* v_fs_2730_ = stack[3].m_obj;
lean_object* v_as_2731_ = stack[4].m_obj;
size_t v_sz_2732_ = stack[5].m_num;
size_t v_i_2733_ = stack[6].m_num;
lean_object* v_b_2734_ = stack[7].m_obj;
lean_object* v___y_2735_ = stack[8].m_obj;
lean_object* v___y_2736_ = stack[9].m_obj;
lean_object* v___y_2737_ = stack[10].m_obj;
lean_object* v___y_2738_ = stack[11].m_obj;
lean_object* v_res_2751_;
v_res_2751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2727_, v___x_2728_, v___x_2729_, v_fs_2730_, v_as_2731_, v_sz_2732_, v_i_2733_, v_b_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
stack->m_obj
 = v_res_2751_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2752_, lean_object* v___x_2753_, lean_object* v___x_2754_, lean_object* v_fs_2755_, lean_object* v_as_2756_, lean_object* v_sz_2757_, lean_object* v_i_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
size_t v_sz_boxed_2765_; size_t v_i_boxed_2766_; lean_object* v_res_2767_; 
v_sz_boxed_2765_ = lean_unbox_usize(v_sz_2757_);
lean_dec(v_sz_2757_);
v_i_boxed_2766_ = lean_unbox_usize(v_i_2758_);
lean_dec(v_i_2758_);
v_res_2767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2752_, v___x_2753_, v___x_2754_, v_fs_2755_, v_as_2756_, v_sz_boxed_2765_, v_i_boxed_2766_, v_b_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec_ref(v_as_2756_);
return v_res_2767_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2768_, lean_object* v___x_2769_, uint8_t v___x_2770_, lean_object* v_targs_2771_, lean_object* v_x_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = l_Lean_mkAppN(v_a_2768_, v_targs_2771_);
v___x_2779_ = l_Lean_mkAppN(v___x_2769_, v_targs_2771_);
v___x_2780_ = l_Lean_Meta_mkPProd(v___x_2778_, v___x_2779_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; uint8_t v___x_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = 0;
v___x_2783_ = 1;
v___x_2784_ = l_Lean_Meta_mkLambdaFVars(v_targs_2771_, v_a_2781_, v___x_2782_, v___x_2770_, v___x_2782_, v___x_2770_, v___x_2783_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2784_;
}
else
{
return v___x_2780_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2768_ = stack[0].m_obj;
lean_object* v___x_2769_ = stack[1].m_obj;
uint8_t v___x_2770_ = stack[2].m_num;
lean_object* v_targs_2771_ = stack[3].m_obj;
lean_object* v_x_2772_ = stack[4].m_obj;
lean_object* v___y_2773_ = stack[5].m_obj;
lean_object* v___y_2774_ = stack[6].m_obj;
lean_object* v___y_2775_ = stack[7].m_obj;
lean_object* v___y_2776_ = stack[8].m_obj;
lean_object* v_res_2785_;
v_res_2785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2768_, v___x_2769_, v___x_2770_, v_targs_2771_, v_x_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
stack->m_obj
 = v_res_2785_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2786_, lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_targs_2789_, lean_object* v_x_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
uint8_t v___x_30756__boxed_2796_; lean_object* v_res_2797_; 
v___x_30756__boxed_2796_ = lean_unbox(v___x_2788_);
v_res_2797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2786_, v___x_2787_, v___x_30756__boxed_2796_, v_targs_2789_, v_x_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec_ref(v_x_2790_);
lean_dec_ref(v_targs_2789_);
return v_res_2797_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2798_, lean_object* v___x_2799_, lean_object* v_as_2800_, size_t v_sz_2801_, size_t v_i_2802_, lean_object* v_b_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = lean_usize_dec_lt(v_i_2802_, v_sz_2801_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2803_);
return v___x_2810_;
}
else
{
lean_object* v_snd_2811_; lean_object* v_fst_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2869_; 
v_snd_2811_ = lean_ctor_get(v_b_2803_, 1);
v_fst_2812_ = lean_ctor_get(v_b_2803_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_b_2803_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2814_ = v_b_2803_;
v_isShared_2815_ = v_isSharedCheck_2869_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snd_2811_);
lean_inc(v_fst_2812_);
lean_dec(v_b_2803_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2869_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_array_2816_; lean_object* v_start_2817_; lean_object* v_stop_2818_; uint8_t v___x_2819_; 
v_array_2816_ = lean_ctor_get(v_snd_2811_, 0);
v_start_2817_ = lean_ctor_get(v_snd_2811_, 1);
v_stop_2818_ = lean_ctor_get(v_snd_2811_, 2);
v___x_2819_ = lean_nat_dec_lt(v_start_2817_, v_stop_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2821_; 
if (v_isShared_2815_ == 0)
{
v___x_2821_ = v___x_2814_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2812_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_snd_2811_);
v___x_2821_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2822_; 
v___x_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
return v___x_2822_;
}
}
else
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2865_; 
lean_inc(v_stop_2818_);
lean_inc(v_start_2817_);
lean_inc_ref(v_array_2816_);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_snd_2811_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; lean_object* v_unused_2867_; lean_object* v_unused_2868_; 
v_unused_2866_ = lean_ctor_get(v_snd_2811_, 2);
lean_dec(v_unused_2866_);
v_unused_2867_ = lean_ctor_get(v_snd_2811_, 1);
lean_dec(v_unused_2867_);
v_unused_2868_ = lean_ctor_get(v_snd_2811_, 0);
lean_dec(v_unused_2868_);
v___x_2825_ = v_snd_2811_;
v_isShared_2826_ = v_isSharedCheck_2865_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v_snd_2811_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2865_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
uint8_t v___x_2827_; lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2827_ = lean_nat_dec_lt(v___x_2798_, v___x_2799_);
v_a_2828_ = lean_array_uget_borrowed(v_as_2800_, v_i_2802_);
v___x_2829_ = lean_array_fget_borrowed(v_array_2816_, v_start_2817_);
v___x_2830_ = lean_box(v___x_2827_);
lean_inc(v___x_2829_);
lean_inc(v_a_2828_);
v___f_2831_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2831_, 0, v_a_2828_);
lean_closure_set(v___f_2831_, 1, v___x_2829_);
lean_closure_set(v___f_2831_, 2, v___x_2830_);
v___x_2832_ = lean_unsigned_to_nat(1u);
v___x_2833_ = lean_nat_add(v_start_2817_, v___x_2832_);
lean_dec(v_start_2817_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 1, v___x_2833_);
v___x_2835_ = v___x_2825_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_array_2816_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_stop_2818_);
v___x_2835_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; 
lean_inc(v___y_2807_);
lean_inc_ref(v___y_2806_);
lean_inc(v___y_2805_);
lean_inc_ref(v___y_2804_);
lean_inc(v_a_2828_);
v___x_2836_ = lean_infer_type(v_a_2828_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; uint8_t v___x_2838_; lean_object* v___x_2839_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = 0;
v___x_2839_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2837_, v___f_2831_, v___x_2838_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Lean_Expr_app___override(v_fst_2812_, v_a_2840_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v___x_2835_);
lean_ctor_set(v___x_2814_, 0, v___x_2841_);
v___x_2843_ = v___x_2814_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2835_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
size_t v___x_2844_; size_t v___x_2845_; 
v___x_2844_ = ((size_t)1ULL);
v___x_2845_ = lean_usize_add(v_i_2802_, v___x_2844_);
v_i_2802_ = v___x_2845_;
v_b_2803_ = v___x_2843_;
goto _start;
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2835_);
lean_del_object(v___x_2814_);
lean_dec(v_fst_2812_);
v_a_2848_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec_ref(v___x_2835_);
lean_dec_ref(v___f_2831_);
lean_del_object(v___x_2814_);
lean_dec(v_fst_2812_);
v_a_2856_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2836_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2836_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2798_ = stack[0].m_obj;
lean_object* v___x_2799_ = stack[1].m_obj;
lean_object* v_as_2800_ = stack[2].m_obj;
size_t v_sz_2801_ = stack[3].m_num;
size_t v_i_2802_ = stack[4].m_num;
lean_object* v_b_2803_ = stack[5].m_obj;
lean_object* v___y_2804_ = stack[6].m_obj;
lean_object* v___y_2805_ = stack[7].m_obj;
lean_object* v___y_2806_ = stack[8].m_obj;
lean_object* v___y_2807_ = stack[9].m_obj;
lean_object* v_res_2870_;
v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2798_, v___x_2799_, v_as_2800_, v_sz_2801_, v_i_2802_, v_b_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
stack->m_obj
 = v_res_2870_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v_as_2873_, lean_object* v_sz_2874_, lean_object* v_i_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
size_t v_sz_boxed_2882_; size_t v_i_boxed_2883_; lean_object* v_res_2884_; 
v_sz_boxed_2882_ = lean_unbox_usize(v_sz_2874_);
lean_dec(v_sz_2874_);
v_i_boxed_2883_ = lean_unbox_usize(v_i_2875_);
lean_dec(v_i_2875_);
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2871_, v___x_2872_, v_as_2873_, v_sz_boxed_2882_, v_i_boxed_2883_, v_b_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_as_2873_);
lean_dec(v___x_2872_);
lean_dec(v___x_2871_);
return v_res_2884_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2885_, size_t v_sz_2886_, size_t v_i_2887_, lean_object* v_b_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v___x_2894_; 
v___x_2894_ = lean_usize_dec_lt(v_i_2887_, v_sz_2886_);
if (v___x_2894_ == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_b_2888_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v_toInductionSubgoal_2897_; lean_object* v_mvarId_2898_; uint8_t v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_a_2896_ = lean_array_uget_borrowed(v_as_2885_, v_i_2887_);
v_toInductionSubgoal_2897_ = lean_ctor_get(v_a_2896_, 0);
v_mvarId_2898_ = lean_ctor_get(v_toInductionSubgoal_2897_, 0);
v___x_2899_ = 0;
v___x_2900_ = lean_box(0);
lean_inc(v_mvarId_2898_);
v___x_2901_ = l_Lean_MVarId_refl(v_mvarId_2898_, v___x_2899_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2901_) == 0)
{
size_t v___x_2902_; size_t v___x_2903_; 
lean_dec_ref_known(v___x_2901_, 1);
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_add(v_i_2887_, v___x_2902_);
v_i_2887_ = v___x_2903_;
v_b_2888_ = v___x_2900_;
goto _start;
}
else
{
return v___x_2901_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2885_ = stack[0].m_obj;
size_t v_sz_2886_ = stack[1].m_num;
size_t v_i_2887_ = stack[2].m_num;
lean_object* v_b_2888_ = stack[3].m_obj;
lean_object* v___y_2889_ = stack[4].m_obj;
lean_object* v___y_2890_ = stack[5].m_obj;
lean_object* v___y_2891_ = stack[6].m_obj;
lean_object* v___y_2892_ = stack[7].m_obj;
lean_object* v_res_2905_;
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2885_, v_sz_2886_, v_i_2887_, v_b_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
stack->m_obj
 = v_res_2905_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2906_, lean_object* v_sz_2907_, lean_object* v_i_2908_, lean_object* v_b_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
size_t v_sz_boxed_2915_; size_t v_i_boxed_2916_; lean_object* v_res_2917_; 
v_sz_boxed_2915_ = lean_unbox_usize(v_sz_2907_);
lean_dec(v_sz_2907_);
v_i_boxed_2916_ = lean_unbox_usize(v_i_2908_);
lean_dec(v_i_2908_);
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2906_, v_sz_boxed_2915_, v_i_boxed_2916_, v_b_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v_as_2906_);
return v_res_2917_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2918_, lean_object* v_tail_2919_, lean_object* v_recName_2920_, lean_object* v___x_2921_, lean_object* v___x_2922_, lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v___x_2927_, lean_object* v___x_2928_, lean_object* v___x_2929_, lean_object* v___x_2930_, lean_object* v___x_2931_, lean_object* v_val_2932_, uint8_t v___x_2933_, lean_object* v_brecOnGoName_2934_, lean_object* v_levelParams_2935_, lean_object* v___x_2936_, lean_object* v_brecOnName_2937_, lean_object* v___x_2938_, lean_object* v_brecOnEqName_2939_, lean_object* v_fs_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; size_t v_sz_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
lean_inc(v___x_2918_);
v___x_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2918_);
lean_ctor_set(v___x_2946_, 1, v_tail_2919_);
v___x_2947_ = l_Lean_Expr_const___override(v_recName_2920_, v___x_2946_);
v___x_2948_ = l_Lean_mkAppN(v___x_2947_, v___x_2921_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v___x_2922_);
v_sz_2950_ = lean_array_size(v___x_2923_);
v___x_2951_ = ((size_t)0ULL);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2924_, v___x_2925_, v___x_2923_, v_sz_2950_, v___x_2951_, v___x_2949_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_fst_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3319_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v_fst_2954_ = lean_ctor_get(v_a_2953_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v_a_2953_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v_a_2953_, 1);
lean_dec(v_unused_3320_);
v___x_2956_ = v_a_2953_;
v_isShared_2957_ = v_isSharedCheck_3319_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_fst_2954_);
lean_dec(v_a_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3319_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
size_t v_sz_2958_; lean_object* v___x_2959_; 
v_sz_2958_ = lean_array_size(v___x_2926_);
lean_inc_ref(v_fs_2940_);
lean_inc_ref(v___x_2927_);
lean_inc_ref(v___x_2923_);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2918_, v___x_2923_, v___x_2927_, v_fs_2940_, v___x_2926_, v_sz_2958_, v___x_2951_, v_fst_2954_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = l_Lean_mkAppN(v_a_2960_, v___x_2928_);
lean_inc_ref_n(v___x_2929_, 3);
v___x_2962_ = l_Lean_Expr_app___override(v___x_2961_, v___x_2929_);
v___x_2963_ = l_Array_append___redArg(v___x_2921_, v___x_2923_);
v___x_2964_ = l_Array_append___redArg(v___x_2963_, v___x_2928_);
v___x_2965_ = lean_mk_empty_array_with_capacity(v___x_2930_);
v___x_2966_ = lean_array_push(v___x_2965_, v___x_2929_);
v___x_2967_ = l_Array_append___redArg(v___x_2964_, v___x_2966_);
lean_dec_ref(v___x_2966_);
v___x_2968_ = l_Array_append___redArg(v___x_2967_, v_fs_2940_);
v___x_2969_ = lean_array_get(v___x_2931_, v___x_2923_, v_val_2932_);
lean_dec_ref(v___x_2923_);
v___x_2970_ = lean_array_push(v___x_2928_, v___x_2929_);
v___x_2971_ = l_Lean_mkAppN(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_array_get(v___x_2931_, v___x_2927_, v_val_2932_);
lean_dec_ref(v___x_2927_);
v___x_2973_ = l_Lean_mkAppN(v___x_2972_, v___x_2970_);
lean_inc_ref(v___x_2971_);
v___x_2974_ = l_Lean_Meta_mkPProd(v___x_2971_, v___x_2973_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; uint8_t v___x_2976_; uint8_t v___x_2977_; lean_object* v___x_2978_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = 0;
v___x_2977_ = 1;
v___x_2978_ = l_Lean_Meta_mkForallFVars(v___x_2968_, v_a_2975_, v___x_2976_, v___x_2933_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l_Lean_Meta_mkLambdaFVars(v___x_2968_, v___x_2962_, v___x_2976_, v___x_2933_, v___x_2976_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3286_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = lean_box(1);
lean_inc(v_levelParams_2935_);
lean_inc(v_brecOnGoName_2934_);
v___x_2983_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2934_, v_levelParams_2935_, v_a_2979_, v_a_2981_, v___x_2982_, v___y_2944_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3286_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3286_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
lean_inc(v_a_2984_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_3285_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_addDecl(v___x_2989_, v___x_2976_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_toConstantVal_2991_; lean_object* v_name_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3282_; 
lean_dec_ref_known(v___x_2990_, 1);
v_toConstantVal_2991_ = lean_ctor_get(v_a_2984_, 0);
lean_inc_ref(v_toConstantVal_2991_);
lean_dec(v_a_2984_);
v_name_2992_ = lean_ctor_get(v_toConstantVal_2991_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_toConstantVal_2991_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; lean_object* v_unused_3284_; 
v_unused_3283_ = lean_ctor_get(v_toConstantVal_2991_, 2);
lean_dec(v_unused_3283_);
v_unused_3284_ = lean_ctor_get(v_toConstantVal_2991_, 1);
lean_dec(v_unused_3284_);
v___x_2994_ = v_toConstantVal_2991_;
v_isShared_2995_ = v_isSharedCheck_3282_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_name_2992_);
lean_dec(v_toConstantVal_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3282_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_ngen_3000_; lean_object* v_auxDeclNGen_3001_; lean_object* v_traceState_3002_; lean_object* v_recordedDeps_3003_; lean_object* v_messages_3004_; lean_object* v_infoState_3005_; lean_object* v_snapshotTasks_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3280_; 
lean_inc(v_name_2992_);
v___x_2996_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2992_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref(v___x_2996_);
v___x_2997_ = lean_st_ref_take(v___y_2944_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3000_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3001_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3002_ = lean_ctor_get(v___x_2997_, 4);
v_recordedDeps_3003_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3004_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3005_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3006_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3280_ == 0)
{
lean_object* v_unused_3281_; 
v_unused_3281_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3281_);
v___x_3008_ = v___x_2997_;
v_isShared_3009_ = v_isSharedCheck_3280_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_snapshotTasks_3006_);
lean_inc(v_infoState_3005_);
lean_inc(v_messages_3004_);
lean_inc(v_recordedDeps_3003_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3001_);
lean_inc(v_ngen_3000_);
lean_inc(v_nextMacroScope_2999_);
lean_inc(v_env_2998_);
lean_dec(v___x_2997_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3280_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3010_ = l_Lean_addProtected(v_env_2998_, v_name_2992_);
v___x_3011_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 5, v___x_3011_);
lean_ctor_set(v___x_3008_, 0, v___x_3010_);
v___x_3013_ = v___x_3008_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v_auxDeclNGen_3001_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v_traceState_3002_);
lean_ctor_set(v_reuseFailAlloc_3279_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3279_, 6, v_recordedDeps_3003_);
lean_ctor_set(v_reuseFailAlloc_3279_, 7, v_messages_3004_);
lean_ctor_set(v_reuseFailAlloc_3279_, 8, v_infoState_3005_);
lean_ctor_set(v_reuseFailAlloc_3279_, 9, v_snapshotTasks_3006_);
v___x_3013_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v_mctx_3016_; lean_object* v_zetaDeltaFVarIds_3017_; lean_object* v_postponed_3018_; lean_object* v_diag_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3277_; 
v___x_3014_ = lean_st_ref_put(v___y_2944_, v___x_3013_);
v___x_3015_ = lean_st_ref_take(v___y_2942_);
v_mctx_3016_ = lean_ctor_get(v___x_3015_, 0);
v_zetaDeltaFVarIds_3017_ = lean_ctor_get(v___x_3015_, 2);
v_postponed_3018_ = lean_ctor_get(v___x_3015_, 3);
v_diag_3019_ = lean_ctor_get(v___x_3015_, 4);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v___x_3015_, 1);
lean_dec(v_unused_3278_);
v___x_3021_ = v___x_3015_;
v_isShared_3022_ = v_isSharedCheck_3277_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_diag_3019_);
lean_inc(v_postponed_3018_);
lean_inc(v_zetaDeltaFVarIds_3017_);
lean_inc(v_mctx_3016_);
lean_dec(v___x_3015_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3277_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3023_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3023_);
v___x_3025_ = v___x_3021_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_mctx_3016_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_zetaDeltaFVarIds_3017_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_postponed_3018_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_diag_3019_);
v___x_3025_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = lean_st_ref_put(v___y_2942_, v___x_3025_);
lean_inc(v___x_2936_);
v___x_3027_ = l_Lean_Expr_const___override(v_brecOnGoName_2934_, v___x_2936_);
v___x_3028_ = l_Lean_mkAppN(v___x_3027_, v___x_2968_);
lean_inc_ref(v___x_3028_);
v___x_3029_ = l_Lean_Meta_mkPProdFstM(v___x_3028_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = l_Lean_Meta_mkLambdaFVars(v___x_2968_, v_a_3030_, v___x_2976_, v___x_2933_, v___x_2976_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___x_3033_ = l_Lean_Meta_mkForallFVars(v___x_2968_, v___x_2971_, v___x_2976_, v___x_2933_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3251_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
lean_inc(v_levelParams_2935_);
v___x_3035_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2937_, v_levelParams_2935_, v_a_3034_, v_a_3032_, v___x_2982_, v___y_2944_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3251_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3251_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
lean_inc(v_a_3036_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set_tag(v___x_3038_, 1);
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_addDecl(v___x_3041_, v___x_2976_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_toConstantVal_3043_; lean_object* v_name_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref_known(v___x_3042_, 1);
v_toConstantVal_3043_ = lean_ctor_get(v_a_3036_, 0);
lean_inc_ref(v_toConstantVal_3043_);
lean_dec(v_a_3036_);
v_name_3044_ = lean_ctor_get(v_toConstantVal_3043_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_toConstantVal_3043_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; lean_object* v_unused_3249_; 
v_unused_3248_ = lean_ctor_get(v_toConstantVal_3043_, 2);
lean_dec(v_unused_3248_);
v_unused_3249_ = lean_ctor_get(v_toConstantVal_3043_, 1);
lean_dec(v_unused_3249_);
v___x_3046_ = v_toConstantVal_3043_;
v_isShared_3047_ = v_isSharedCheck_3247_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_name_3044_);
lean_dec(v_toConstantVal_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3247_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v_env_3050_; lean_object* v_nextMacroScope_3051_; lean_object* v_ngen_3052_; lean_object* v_auxDeclNGen_3053_; lean_object* v_traceState_3054_; lean_object* v_recordedDeps_3055_; lean_object* v_messages_3056_; lean_object* v_infoState_3057_; lean_object* v_snapshotTasks_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3245_; 
lean_inc(v_name_3044_);
v___x_3048_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_3044_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref(v___x_3048_);
v___x_3049_ = lean_st_ref_take(v___y_2944_);
v_env_3050_ = lean_ctor_get(v___x_3049_, 0);
v_nextMacroScope_3051_ = lean_ctor_get(v___x_3049_, 1);
v_ngen_3052_ = lean_ctor_get(v___x_3049_, 2);
v_auxDeclNGen_3053_ = lean_ctor_get(v___x_3049_, 3);
v_traceState_3054_ = lean_ctor_get(v___x_3049_, 4);
v_recordedDeps_3055_ = lean_ctor_get(v___x_3049_, 6);
v_messages_3056_ = lean_ctor_get(v___x_3049_, 7);
v_infoState_3057_ = lean_ctor_get(v___x_3049_, 8);
v_snapshotTasks_3058_ = lean_ctor_get(v___x_3049_, 9);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3245_ == 0)
{
lean_object* v_unused_3246_; 
v_unused_3246_ = lean_ctor_get(v___x_3049_, 5);
lean_dec(v_unused_3246_);
v___x_3060_ = v___x_3049_;
v_isShared_3061_ = v_isSharedCheck_3245_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snapshotTasks_3058_);
lean_inc(v_infoState_3057_);
lean_inc(v_messages_3056_);
lean_inc(v_recordedDeps_3055_);
lean_inc(v_traceState_3054_);
lean_inc(v_auxDeclNGen_3053_);
lean_inc(v_ngen_3052_);
lean_inc(v_nextMacroScope_3051_);
lean_inc(v_env_3050_);
lean_dec(v___x_3049_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3245_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
lean_inc(v_name_3044_);
v___x_3062_ = l_Lean_markAuxRecursor(v_env_3050_, v_name_3044_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 5, v___x_3011_);
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_nextMacroScope_3051_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_ngen_3052_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_auxDeclNGen_3053_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_traceState_3054_);
lean_ctor_set(v_reuseFailAlloc_3244_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3244_, 6, v_recordedDeps_3055_);
lean_ctor_set(v_reuseFailAlloc_3244_, 7, v_messages_3056_);
lean_ctor_set(v_reuseFailAlloc_3244_, 8, v_infoState_3057_);
lean_ctor_set(v_reuseFailAlloc_3244_, 9, v_snapshotTasks_3058_);
v___x_3064_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_mctx_3067_; lean_object* v_zetaDeltaFVarIds_3068_; lean_object* v_postponed_3069_; lean_object* v_diag_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3242_; 
v___x_3065_ = lean_st_ref_put(v___y_2944_, v___x_3064_);
v___x_3066_ = lean_st_ref_take(v___y_2942_);
v_mctx_3067_ = lean_ctor_get(v___x_3066_, 0);
v_zetaDeltaFVarIds_3068_ = lean_ctor_get(v___x_3066_, 2);
v_postponed_3069_ = lean_ctor_get(v___x_3066_, 3);
v_diag_3070_ = lean_ctor_get(v___x_3066_, 4);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3066_, 1);
lean_dec(v_unused_3243_);
v___x_3072_ = v___x_3066_;
v_isShared_3073_ = v_isSharedCheck_3242_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_diag_3070_);
lean_inc(v_postponed_3069_);
lean_inc(v_zetaDeltaFVarIds_3068_);
lean_inc(v_mctx_3067_);
lean_dec(v___x_3066_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3242_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v___x_3023_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_mctx_3067_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_zetaDeltaFVarIds_3068_);
lean_ctor_set(v_reuseFailAlloc_3241_, 3, v_postponed_3069_);
lean_ctor_set(v_reuseFailAlloc_3241_, 4, v_diag_3070_);
v___x_3075_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v_env_3078_; lean_object* v_nextMacroScope_3079_; lean_object* v_ngen_3080_; lean_object* v_auxDeclNGen_3081_; lean_object* v_traceState_3082_; lean_object* v_recordedDeps_3083_; lean_object* v_messages_3084_; lean_object* v_infoState_3085_; lean_object* v_snapshotTasks_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3239_; 
v___x_3076_ = lean_st_ref_put(v___y_2942_, v___x_3075_);
v___x_3077_ = lean_st_ref_take(v___y_2944_);
v_env_3078_ = lean_ctor_get(v___x_3077_, 0);
v_nextMacroScope_3079_ = lean_ctor_get(v___x_3077_, 1);
v_ngen_3080_ = lean_ctor_get(v___x_3077_, 2);
v_auxDeclNGen_3081_ = lean_ctor_get(v___x_3077_, 3);
v_traceState_3082_ = lean_ctor_get(v___x_3077_, 4);
v_recordedDeps_3083_ = lean_ctor_get(v___x_3077_, 6);
v_messages_3084_ = lean_ctor_get(v___x_3077_, 7);
v_infoState_3085_ = lean_ctor_get(v___x_3077_, 8);
v_snapshotTasks_3086_ = lean_ctor_get(v___x_3077_, 9);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; 
v_unused_3240_ = lean_ctor_get(v___x_3077_, 5);
lean_dec(v_unused_3240_);
v___x_3088_ = v___x_3077_;
v_isShared_3089_ = v_isSharedCheck_3239_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_snapshotTasks_3086_);
lean_inc(v_infoState_3085_);
lean_inc(v_messages_3084_);
lean_inc(v_recordedDeps_3083_);
lean_inc(v_traceState_3082_);
lean_inc(v_auxDeclNGen_3081_);
lean_inc(v_ngen_3080_);
lean_inc(v_nextMacroScope_3079_);
lean_inc(v_env_3078_);
lean_dec(v___x_3077_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3239_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
lean_inc(v_name_3044_);
v___x_3090_ = l_Lean_addProtected(v_env_3078_, v_name_3044_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 5, v___x_3011_);
lean_ctor_set(v___x_3088_, 0, v___x_3090_);
v___x_3092_ = v___x_3088_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_nextMacroScope_3079_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_ngen_3080_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_auxDeclNGen_3081_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_traceState_3082_);
lean_ctor_set(v_reuseFailAlloc_3238_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3238_, 6, v_recordedDeps_3083_);
lean_ctor_set(v_reuseFailAlloc_3238_, 7, v_messages_3084_);
lean_ctor_set(v_reuseFailAlloc_3238_, 8, v_infoState_3085_);
lean_ctor_set(v_reuseFailAlloc_3238_, 9, v_snapshotTasks_3086_);
v___x_3092_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v_mctx_3095_; lean_object* v_zetaDeltaFVarIds_3096_; lean_object* v_postponed_3097_; lean_object* v_diag_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3236_; 
v___x_3093_ = lean_st_ref_put(v___y_2944_, v___x_3092_);
v___x_3094_ = lean_st_ref_take(v___y_2942_);
v_mctx_3095_ = lean_ctor_get(v___x_3094_, 0);
v_zetaDeltaFVarIds_3096_ = lean_ctor_get(v___x_3094_, 2);
v_postponed_3097_ = lean_ctor_get(v___x_3094_, 3);
v_diag_3098_ = lean_ctor_get(v___x_3094_, 4);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3094_, 1);
lean_dec(v_unused_3237_);
v___x_3100_ = v___x_3094_;
v_isShared_3101_ = v_isSharedCheck_3236_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_diag_3098_);
lean_inc(v_postponed_3097_);
lean_inc(v_zetaDeltaFVarIds_3096_);
lean_inc(v_mctx_3095_);
lean_dec(v___x_3094_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3236_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 1, v___x_3023_);
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_mctx_3095_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_zetaDeltaFVarIds_3096_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v_postponed_3097_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v_diag_3098_);
v___x_3103_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3104_ = lean_st_ref_put(v___y_2942_, v___x_3103_);
v___x_3105_ = l_Lean_Expr_const___override(v_name_3044_, v___x_2936_);
v___x_3106_ = l_Lean_mkAppN(v___x_3105_, v___x_2968_);
v___x_3107_ = lean_array_get(v___x_2931_, v_fs_2940_, v_val_2932_);
lean_dec_ref(v_fs_2940_);
v___x_3108_ = l_Lean_mkAppN(v___x_3107_, v___x_2970_);
lean_dec_ref(v___x_2970_);
v___x_3109_ = l_Lean_Meta_mkPProdSndM(v___x_3028_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___x_3109_, 1);
v___x_3111_ = l_Lean_Expr_app___override(v___x_3108_, v_a_3110_);
v___x_3112_ = l_Lean_Meta_mkEq(v___x_3106_, v___x_3111_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_n(v_a_3113_, 2);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = lean_box(0);
v___x_3115_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3113_, v___x_3114_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3117_ = l_Lean_Expr_mvarId_x21(v_a_3116_);
v___x_3118_ = l_Lean_Expr_fvarId_x21(v___x_2929_);
lean_dec_ref(v___x_2929_);
v___x_3119_ = lean_mk_empty_array_with_capacity(v___x_2938_);
v___x_3120_ = lean_box(0);
v___x_3121_ = l_Lean_MVarId_cases(v___x_3117_, v___x_3118_, v___x_3119_, v___x_2976_, v___x_3120_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; size_t v_sz_3124_; lean_object* v___x_3125_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = lean_box(0);
v_sz_3124_ = lean_array_size(v_a_3122_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3122_, v_sz_3124_, v___x_2951_, v___x_3123_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v_a_3122_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v___x_3126_; lean_object* v_a_3127_; lean_object* v___x_3128_; 
lean_dec_ref_known(v___x_3125_, 1);
v___x_3126_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3116_, v___y_2942_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = l_Lean_Meta_mkForallFVars(v___x_2968_, v_a_3113_, v___x_2976_, v___x_2933_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3130_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
v___x_3130_ = l_Lean_Meta_mkLambdaFVars(v___x_2968_, v_a_3127_, v___x_2976_, v___x_2933_, v___x_2976_, v___x_2933_, v___x_2977_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec_ref(v___x_2968_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
lean_inc(v_brecOnEqName_2939_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 2, v_a_3129_);
lean_ctor_set(v___x_3046_, 1, v_levelParams_2935_);
lean_ctor_set(v___x_3046_, 0, v_brecOnEqName_2939_);
v___x_3133_ = v___x_3046_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_brecOnEqName_2939_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_levelParams_2935_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_a_3129_);
v___x_3133_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_box(0);
lean_inc(v_brecOnEqName_2939_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 1);
lean_ctor_set(v___x_2956_, 1, v___x_3134_);
lean_ctor_set(v___x_2956_, 0, v_brecOnEqName_2939_);
v___x_3136_ = v___x_2956_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_brecOnEqName_2939_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 2, v___x_3136_);
lean_ctor_set(v___x_2994_, 1, v_a_3131_);
lean_ctor_set(v___x_2994_, 0, v___x_3133_);
v___x_3138_ = v___x_2994_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_a_3131_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v_a_3140_; lean_object* v___x_3141_; 
v___x_3139_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3138_, v___y_2944_);
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v___x_3141_ = l_Lean_addDecl(v_a_3140_, v___x_2976_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3182_; 
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3183_);
v___x_3143_ = v___x_3141_;
v_isShared_3144_ = v_isSharedCheck_3182_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v___x_3141_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3182_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v_env_3146_; lean_object* v_nextMacroScope_3147_; lean_object* v_ngen_3148_; lean_object* v_auxDeclNGen_3149_; lean_object* v_traceState_3150_; lean_object* v_recordedDeps_3151_; lean_object* v_messages_3152_; lean_object* v_infoState_3153_; lean_object* v_snapshotTasks_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3180_; 
v___x_3145_ = lean_st_ref_take(v___y_2944_);
v_env_3146_ = lean_ctor_get(v___x_3145_, 0);
v_nextMacroScope_3147_ = lean_ctor_get(v___x_3145_, 1);
v_ngen_3148_ = lean_ctor_get(v___x_3145_, 2);
v_auxDeclNGen_3149_ = lean_ctor_get(v___x_3145_, 3);
v_traceState_3150_ = lean_ctor_get(v___x_3145_, 4);
v_recordedDeps_3151_ = lean_ctor_get(v___x_3145_, 6);
v_messages_3152_ = lean_ctor_get(v___x_3145_, 7);
v_infoState_3153_ = lean_ctor_get(v___x_3145_, 8);
v_snapshotTasks_3154_ = lean_ctor_get(v___x_3145_, 9);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3145_, 5);
lean_dec(v_unused_3181_);
v___x_3156_ = v___x_3145_;
v_isShared_3157_ = v_isSharedCheck_3180_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_snapshotTasks_3154_);
lean_inc(v_infoState_3153_);
lean_inc(v_messages_3152_);
lean_inc(v_recordedDeps_3151_);
lean_inc(v_traceState_3150_);
lean_inc(v_auxDeclNGen_3149_);
lean_inc(v_ngen_3148_);
lean_inc(v_nextMacroScope_3147_);
lean_inc(v_env_3146_);
lean_dec(v___x_3145_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3180_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3158_ = l_Lean_addProtected(v_env_3146_, v_brecOnEqName_2939_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 5, v___x_3011_);
lean_ctor_set(v___x_3156_, 0, v___x_3158_);
v___x_3160_ = v___x_3156_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_nextMacroScope_3147_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_ngen_3148_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_auxDeclNGen_3149_);
lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_traceState_3150_);
lean_ctor_set(v_reuseFailAlloc_3179_, 5, v___x_3011_);
lean_ctor_set(v_reuseFailAlloc_3179_, 6, v_recordedDeps_3151_);
lean_ctor_set(v_reuseFailAlloc_3179_, 7, v_messages_3152_);
lean_ctor_set(v_reuseFailAlloc_3179_, 8, v_infoState_3153_);
lean_ctor_set(v_reuseFailAlloc_3179_, 9, v_snapshotTasks_3154_);
v___x_3160_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v_mctx_3163_; lean_object* v_zetaDeltaFVarIds_3164_; lean_object* v_postponed_3165_; lean_object* v_diag_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3177_; 
v___x_3161_ = lean_st_ref_put(v___y_2944_, v___x_3160_);
v___x_3162_ = lean_st_ref_take(v___y_2942_);
v_mctx_3163_ = lean_ctor_get(v___x_3162_, 0);
v_zetaDeltaFVarIds_3164_ = lean_ctor_get(v___x_3162_, 2);
v_postponed_3165_ = lean_ctor_get(v___x_3162_, 3);
v_diag_3166_ = lean_ctor_get(v___x_3162_, 4);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3162_, 1);
lean_dec(v_unused_3178_);
v___x_3168_ = v___x_3162_;
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_diag_3166_);
lean_inc(v_postponed_3165_);
lean_inc(v_zetaDeltaFVarIds_3164_);
lean_inc(v_mctx_3163_);
lean_dec(v___x_3162_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3177_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 1, v___x_3023_);
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_mctx_3163_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_zetaDeltaFVarIds_3164_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v_postponed_3165_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v_diag_3166_);
v___x_3171_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
v___x_3172_ = lean_st_ref_put(v___y_2942_, v___x_3171_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3123_);
v___x_3174_ = v___x_3143_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3123_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2939_);
return v___x_3141_;
}
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_a_3129_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
v_a_3187_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3130_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3130_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_3127_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
v_a_3195_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3128_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3128_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
else
{
lean_dec(v_a_3116_);
lean_dec(v_a_3113_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
return v___x_3125_;
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_a_3116_);
lean_dec(v_a_3113_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
v_a_3203_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3121_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3121_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec(v_a_3113_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3211_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3115_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3115_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3219_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3112_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3112_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v___x_3108_);
lean_dec_ref(v___x_3106_);
lean_del_object(v___x_3046_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3227_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3109_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3109_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
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
lean_dec(v_a_3036_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_a_3032_);
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3252_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3033_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3033_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3260_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3031_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3031_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v___x_3028_);
lean_del_object(v___x_2994_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec_ref(v___x_2929_);
v_a_3268_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3029_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3029_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
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
lean_dec(v_a_2984_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec(v_a_2979_);
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
v_a_3287_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_2980_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_2980_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
v_a_3295_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_2978_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_2978_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref(v___x_2971_);
lean_dec_ref(v___x_2970_);
lean_dec_ref(v___x_2968_);
lean_dec_ref(v___x_2962_);
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
v_a_3303_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_2974_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_2974_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_del_object(v___x_2956_);
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v___x_2927_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2921_);
v_a_3311_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_2959_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_2959_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref(v_fs_2940_);
lean_dec(v_brecOnEqName_2939_);
lean_dec(v_brecOnName_2937_);
lean_dec(v___x_2936_);
lean_dec(v_levelParams_2935_);
lean_dec(v_brecOnGoName_2934_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v___x_2928_);
lean_dec_ref(v___x_2927_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2918_);
v_a_3321_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_2952_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_2952_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2918_ = stack[0].m_obj;
lean_object* v_tail_2919_ = stack[1].m_obj;
lean_object* v_recName_2920_ = stack[2].m_obj;
lean_object* v___x_2921_ = stack[3].m_obj;
lean_object* v___x_2922_ = stack[4].m_obj;
lean_object* v___x_2923_ = stack[5].m_obj;
lean_object* v___x_2924_ = stack[6].m_obj;
lean_object* v___x_2925_ = stack[7].m_obj;
lean_object* v___x_2926_ = stack[8].m_obj;
lean_object* v___x_2927_ = stack[9].m_obj;
lean_object* v___x_2928_ = stack[10].m_obj;
lean_object* v___x_2929_ = stack[11].m_obj;
lean_object* v___x_2930_ = stack[12].m_obj;
lean_object* v___x_2931_ = stack[13].m_obj;
lean_object* v_val_2932_ = stack[14].m_obj;
uint8_t v___x_2933_ = stack[15].m_num;
lean_object* v_brecOnGoName_2934_ = stack[16].m_obj;
lean_object* v_levelParams_2935_ = stack[17].m_obj;
lean_object* v___x_2936_ = stack[18].m_obj;
lean_object* v_brecOnName_2937_ = stack[19].m_obj;
lean_object* v___x_2938_ = stack[20].m_obj;
lean_object* v_brecOnEqName_2939_ = stack[21].m_obj;
lean_object* v_fs_2940_ = stack[22].m_obj;
lean_object* v___y_2941_ = stack[23].m_obj;
lean_object* v___y_2942_ = stack[24].m_obj;
lean_object* v___y_2943_ = stack[25].m_obj;
lean_object* v___y_2944_ = stack[26].m_obj;
lean_object* v_res_3329_;
v_res_3329_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_2918_, v_tail_2919_, v_recName_2920_, v___x_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v___x_2925_, v___x_2926_, v___x_2927_, v___x_2928_, v___x_2929_, v___x_2930_, v___x_2931_, v_val_2932_, v___x_2933_, v_brecOnGoName_2934_, v_levelParams_2935_, v___x_2936_, v_brecOnName_2937_, v___x_2938_, v_brecOnEqName_2939_, v_fs_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
stack->m_obj
 = v_res_3329_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3330_ = _args[0];
lean_object* v_tail_3331_ = _args[1];
lean_object* v_recName_3332_ = _args[2];
lean_object* v___x_3333_ = _args[3];
lean_object* v___x_3334_ = _args[4];
lean_object* v___x_3335_ = _args[5];
lean_object* v___x_3336_ = _args[6];
lean_object* v___x_3337_ = _args[7];
lean_object* v___x_3338_ = _args[8];
lean_object* v___x_3339_ = _args[9];
lean_object* v___x_3340_ = _args[10];
lean_object* v___x_3341_ = _args[11];
lean_object* v___x_3342_ = _args[12];
lean_object* v___x_3343_ = _args[13];
lean_object* v_val_3344_ = _args[14];
lean_object* v___x_3345_ = _args[15];
lean_object* v_brecOnGoName_3346_ = _args[16];
lean_object* v_levelParams_3347_ = _args[17];
lean_object* v___x_3348_ = _args[18];
lean_object* v_brecOnName_3349_ = _args[19];
lean_object* v___x_3350_ = _args[20];
lean_object* v_brecOnEqName_3351_ = _args[21];
lean_object* v_fs_3352_ = _args[22];
lean_object* v___y_3353_ = _args[23];
lean_object* v___y_3354_ = _args[24];
lean_object* v___y_3355_ = _args[25];
lean_object* v___y_3356_ = _args[26];
lean_object* v___y_3357_ = _args[27];
_start:
{
uint8_t v___x_31095__boxed_3358_; lean_object* v_res_3359_; 
v___x_31095__boxed_3358_ = lean_unbox(v___x_3345_);
v_res_3359_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3330_, v_tail_3331_, v_recName_3332_, v___x_3333_, v___x_3334_, v___x_3335_, v___x_3336_, v___x_3337_, v___x_3338_, v___x_3339_, v___x_3340_, v___x_3341_, v___x_3342_, v___x_3343_, v_val_3344_, v___x_31095__boxed_3358_, v_brecOnGoName_3346_, v_levelParams_3347_, v___x_3348_, v_brecOnName_3349_, v___x_3350_, v_brecOnEqName_3351_, v_fs_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___x_3350_);
lean_dec(v_val_3344_);
lean_dec_ref(v___x_3343_);
lean_dec(v___x_3342_);
lean_dec_ref(v___x_3338_);
lean_dec(v___x_3337_);
lean_dec(v___x_3336_);
return v_res_3359_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3360_, lean_object* v_a_3361_, uint8_t v___x_3362_, lean_object* v_f_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; 
lean_inc_ref(v_targs_3360_);
v___x_3369_ = lean_array_push(v_targs_3360_, v_f_3363_);
v___x_3370_ = l_Lean_mkAppN(v_a_3361_, v_targs_3360_);
lean_dec_ref(v_targs_3360_);
v___x_3371_ = 0;
v___x_3372_ = 1;
v___x_3373_ = l_Lean_Meta_mkForallFVars(v___x_3369_, v___x_3370_, v___x_3371_, v___x_3362_, v___x_3362_, v___x_3372_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec_ref(v___x_3369_);
return v___x_3373_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_targs_3360_ = stack[0].m_obj;
lean_object* v_a_3361_ = stack[1].m_obj;
uint8_t v___x_3362_ = stack[2].m_num;
lean_object* v_f_3363_ = stack[3].m_obj;
lean_object* v___y_3364_ = stack[4].m_obj;
lean_object* v___y_3365_ = stack[5].m_obj;
lean_object* v___y_3366_ = stack[6].m_obj;
lean_object* v___y_3367_ = stack[7].m_obj;
lean_object* v_res_3374_;
v_res_3374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3360_, v_a_3361_, v___x_3362_, v_f_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
stack->m_obj
 = v_res_3374_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3375_, lean_object* v_a_3376_, lean_object* v___x_3377_, lean_object* v_f_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
uint8_t v___x_32176__boxed_3384_; lean_object* v_res_3385_; 
v___x_32176__boxed_3384_ = lean_unbox(v___x_3377_);
v_res_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3375_, v_a_3376_, v___x_32176__boxed_3384_, v_f_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
return v_res_3385_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3389_, uint8_t v___x_3390_, lean_object* v___x_3391_, lean_object* v_targs_3392_, lean_object* v_x_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v___f_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3399_ = lean_box(v___x_3390_);
lean_inc_ref(v_targs_3392_);
v___f_3400_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3400_, 0, v_targs_3392_);
lean_closure_set(v___f_3400_, 1, v_a_3389_);
lean_closure_set(v___f_3400_, 2, v___x_3399_);
v___x_3401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3402_ = l_Lean_mkAppN(v___x_3391_, v_targs_3392_);
lean_dec_ref(v_targs_3392_);
v___x_3403_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3401_, v___x_3402_, v___f_3400_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3403_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3389_ = stack[0].m_obj;
uint8_t v___x_3390_ = stack[1].m_num;
lean_object* v___x_3391_ = stack[2].m_obj;
lean_object* v_targs_3392_ = stack[3].m_obj;
lean_object* v_x_3393_ = stack[4].m_obj;
lean_object* v___y_3394_ = stack[5].m_obj;
lean_object* v___y_3395_ = stack[6].m_obj;
lean_object* v___y_3396_ = stack[7].m_obj;
lean_object* v___y_3397_ = stack[8].m_obj;
lean_object* v_res_3404_;
v_res_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3389_, v___x_3390_, v___x_3391_, v_targs_3392_, v_x_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
stack->m_obj
 = v_res_3404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3405_, lean_object* v___x_3406_, lean_object* v___x_3407_, lean_object* v_targs_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_32227__boxed_3415_; lean_object* v_res_3416_; 
v___x_32227__boxed_3415_ = lean_unbox(v___x_3406_);
v_res_3416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3405_, v___x_32227__boxed_3415_, v___x_3407_, v_targs_3408_, v_x_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v_x_3409_);
return v_res_3416_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_a_3417_);
return v___x_3424_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3417_ = stack[0].m_obj;
lean_object* v_x_3418_ = stack[1].m_obj;
lean_object* v___y_3419_ = stack[2].m_obj;
lean_object* v___y_3420_ = stack[3].m_obj;
lean_object* v___y_3421_ = stack[4].m_obj;
lean_object* v___y_3422_ = stack[5].m_obj;
lean_object* v_res_3425_;
v_res_3425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3417_, v_x_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
stack->m_obj
 = v_res_3425_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3426_, lean_object* v_x_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3426_, v_x_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec_ref(v_x_3427_);
return v_res_3433_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3435_, lean_object* v___x_3436_, lean_object* v_as_3437_, size_t v_sz_3438_, size_t v_i_3439_, lean_object* v_b_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3439_, v_sz_3438_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_b_3440_);
return v___x_3447_;
}
else
{
lean_object* v_snd_3448_; lean_object* v_fst_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3546_; 
v_snd_3448_ = lean_ctor_get(v_b_3440_, 1);
v_fst_3449_ = lean_ctor_get(v_b_3440_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_b_3440_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3451_ = v_b_3440_;
v_isShared_3452_ = v_isSharedCheck_3546_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3448_);
lean_inc(v_fst_3449_);
lean_dec(v_b_3440_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3546_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v_fst_3453_; lean_object* v_snd_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3545_; 
v_fst_3453_ = lean_ctor_get(v_snd_3448_, 0);
v_snd_3454_ = lean_ctor_get(v_snd_3448_, 1);
v_isSharedCheck_3545_ = !lean_is_exclusive(v_snd_3448_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3456_ = v_snd_3448_;
v_isShared_3457_ = v_isSharedCheck_3545_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_snd_3454_);
lean_inc(v_fst_3453_);
lean_dec(v_snd_3448_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3545_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v_next_3466_; 
v_next_3466_ = lean_ctor_get(v_snd_3454_, 0);
lean_inc(v_next_3466_);
if (lean_obj_tag(v_next_3466_) == 0)
{
goto v___jp_3458_;
}
else
{
lean_object* v_upperBound_3467_; lean_object* v_val_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3544_; 
v_upperBound_3467_ = lean_ctor_get(v_snd_3454_, 1);
v_val_3468_ = lean_ctor_get(v_next_3466_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_next_3466_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3470_ = v_next_3466_;
v_isShared_3471_ = v_isSharedCheck_3544_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_val_3468_);
lean_dec(v_next_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3544_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint8_t v___x_3472_; 
v___x_3472_ = lean_nat_dec_lt(v_val_3468_, v_upperBound_3467_);
if (v___x_3472_ == 0)
{
lean_del_object(v___x_3470_);
lean_dec(v_val_3468_);
goto v___jp_3458_;
}
else
{
lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3541_; 
lean_inc(v_upperBound_3467_);
lean_del_object(v___x_3456_);
lean_del_object(v___x_3451_);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_snd_3454_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; lean_object* v_unused_3543_; 
v_unused_3542_ = lean_ctor_get(v_snd_3454_, 1);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_snd_3454_, 0);
lean_dec(v_unused_3543_);
v___x_3474_ = v_snd_3454_;
v_isShared_3475_ = v_isSharedCheck_3541_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v_snd_3454_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3541_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_array_3476_; lean_object* v_start_3477_; lean_object* v_stop_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_array_3476_ = lean_ctor_get(v_fst_3453_, 0);
v_start_3477_ = lean_ctor_get(v_fst_3453_, 1);
v_stop_3478_ = lean_ctor_get(v_fst_3453_, 2);
v___x_3479_ = lean_unsigned_to_nat(1u);
v___x_3480_ = lean_nat_add(v_val_3468_, v___x_3479_);
lean_dec(v_val_3468_);
lean_inc(v___x_3480_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3480_);
v___x_3482_ = v___x_3470_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3484_; 
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3482_);
v___x_3484_ = v___x_3474_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_upperBound_3467_);
v___x_3484_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_lt(v_start_3477_, v_stop_3478_);
if (v___x_3485_ == 0)
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec(v___x_3480_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_fst_3453_);
lean_ctor_set(v___x_3486_, 1, v___x_3484_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_fst_3449_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
return v___x_3488_;
}
else
{
lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3535_; 
lean_inc(v_stop_3478_);
lean_inc(v_start_3477_);
lean_inc_ref(v_array_3476_);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_fst_3453_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; lean_object* v_unused_3537_; lean_object* v_unused_3538_; 
v_unused_3536_ = lean_ctor_get(v_fst_3453_, 2);
lean_dec(v_unused_3536_);
v_unused_3537_ = lean_ctor_get(v_fst_3453_, 1);
lean_dec(v_unused_3537_);
v_unused_3538_ = lean_ctor_get(v_fst_3453_, 0);
lean_dec(v_unused_3538_);
v___x_3490_ = v_fst_3453_;
v_isShared_3491_ = v_isSharedCheck_3535_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v_fst_3453_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3535_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
uint8_t v___x_3492_; lean_object* v_a_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3492_ = lean_nat_dec_lt(v___x_3435_, v___x_3436_);
v_a_3493_ = lean_array_uget_borrowed(v_as_3437_, v_i_3439_);
v___x_3494_ = lean_array_fget_borrowed(v_array_3476_, v_start_3477_);
v___x_3495_ = lean_box(v___x_3492_);
lean_inc(v___x_3494_);
lean_inc(v_a_3493_);
v___f_3496_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3496_, 0, v_a_3493_);
lean_closure_set(v___f_3496_, 1, v___x_3495_);
lean_closure_set(v___f_3496_, 2, v___x_3494_);
v___x_3497_ = lean_nat_add(v_start_3477_, v___x_3479_);
lean_dec(v_start_3477_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v___x_3497_);
v___x_3499_ = v___x_3490_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_array_3476_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_stop_3478_);
v___x_3499_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
lean_object* v___x_3500_; 
lean_inc(v___y_3444_);
lean_inc_ref(v___y_3443_);
lean_inc(v___y_3442_);
lean_inc_ref(v___y_3441_);
lean_inc(v_a_3493_);
v___x_3500_ = lean_infer_type(v_a_3493_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = 0;
v___x_3503_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3501_, v___f_3496_, v___x_3502_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___f_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; size_t v___x_3515_; size_t v___x_3516_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___f_3505_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3505_, 0, v_a_3504_);
v___x_3506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3507_ = l_Nat_reprFast(v___x_3480_);
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
lean_dec_ref(v___x_3507_);
v___x_3509_ = lean_box(0);
v___x_3510_ = l_Lean_Name_str___override(v___x_3509_, v___x_3508_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v___f_3505_);
v___x_3512_ = lean_array_push(v_fst_3449_, v___x_3511_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3499_);
lean_ctor_set(v___x_3513_, 1, v___x_3484_);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3512_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3439_, v___x_3515_);
v_i_3439_ = v___x_3516_;
v_b_3440_ = v___x_3514_;
goto _start;
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_3499_);
lean_dec_ref(v___x_3484_);
lean_dec(v___x_3480_);
lean_dec(v_fst_3449_);
v_a_3518_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3503_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3503_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v___x_3499_);
lean_dec_ref(v___f_3496_);
lean_dec_ref(v___x_3484_);
lean_dec(v___x_3480_);
lean_dec(v_fst_3449_);
v_a_3526_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3500_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3500_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
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
v___jp_3458_:
{
lean_object* v___x_3460_; 
if (v_isShared_3457_ == 0)
{
v___x_3460_ = v___x_3456_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_fst_3453_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_snd_3454_);
v___x_3460_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___x_3460_);
v___x_3462_ = v___x_3451_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_fst_3449_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
return v___x_3463_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3435_ = stack[0].m_obj;
lean_object* v___x_3436_ = stack[1].m_obj;
lean_object* v_as_3437_ = stack[2].m_obj;
size_t v_sz_3438_ = stack[3].m_num;
size_t v_i_3439_ = stack[4].m_num;
lean_object* v_b_3440_ = stack[5].m_obj;
lean_object* v___y_3441_ = stack[6].m_obj;
lean_object* v___y_3442_ = stack[7].m_obj;
lean_object* v___y_3443_ = stack[8].m_obj;
lean_object* v___y_3444_ = stack[9].m_obj;
lean_object* v_res_3547_;
v_res_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3435_, v___x_3436_, v_as_3437_, v_sz_3438_, v_i_3439_, v_b_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
stack->m_obj
 = v_res_3547_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3548_, lean_object* v___x_3549_, lean_object* v_as_3550_, lean_object* v_sz_3551_, lean_object* v_i_3552_, lean_object* v_b_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
size_t v_sz_boxed_3559_; size_t v_i_boxed_3560_; lean_object* v_res_3561_; 
v_sz_boxed_3559_ = lean_unbox_usize(v_sz_3551_);
lean_dec(v_sz_3551_);
v_i_boxed_3560_ = lean_unbox_usize(v_i_3552_);
lean_dec(v_i_3552_);
v_res_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3548_, v___x_3549_, v_as_3550_, v_sz_boxed_3559_, v_i_boxed_3560_, v_b_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec_ref(v_as_3550_);
lean_dec(v___x_3549_);
lean_dec(v___x_3548_);
return v_res_3561_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3562_, size_t v_i_3563_, lean_object* v_bs_3564_){
_start:
{
uint8_t v___x_3565_; 
v___x_3565_ = lean_usize_dec_lt(v_i_3563_, v_sz_3562_);
if (v___x_3565_ == 0)
{
return v_bs_3564_;
}
else
{
lean_object* v_v_3566_; lean_object* v_fst_3567_; lean_object* v_snd_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3584_; 
v_v_3566_ = lean_array_uget(v_bs_3564_, v_i_3563_);
v_fst_3567_ = lean_ctor_get(v_v_3566_, 0);
v_snd_3568_ = lean_ctor_get(v_v_3566_, 1);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_v_3566_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3570_ = v_v_3566_;
v_isShared_3571_ = v_isSharedCheck_3584_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snd_3568_);
lean_inc(v_fst_3567_);
lean_dec(v_v_3566_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3584_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v_bs_x27_3573_; uint8_t v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3572_ = lean_unsigned_to_nat(0u);
v_bs_x27_3573_ = lean_array_uset(v_bs_3564_, v_i_3563_, v___x_3572_);
v___x_3574_ = 0;
v___x_3575_ = lean_box(v___x_3574_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3575_);
v___x_3577_ = v___x_3570_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_snd_3568_);
v___x_3577_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3578_; size_t v___x_3579_; size_t v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_fst_3567_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_add(v_i_3563_, v___x_3579_);
v___x_3581_ = lean_array_uset(v_bs_x27_3573_, v_i_3563_, v___x_3578_);
v_i_3563_ = v___x_3580_;
v_bs_3564_ = v___x_3581_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3562_ = stack[0].m_num;
size_t v_i_3563_ = stack[1].m_num;
lean_object* v_bs_3564_ = stack[2].m_obj;
lean_object* v_res_3585_;
v_res_3585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3562_, v_i_3563_, v_bs_3564_);
stack->m_obj
 = v_res_3585_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3586_, lean_object* v_i_3587_, lean_object* v_bs_3588_){
_start:
{
size_t v_sz_boxed_3589_; size_t v_i_boxed_3590_; lean_object* v_res_3591_; 
v_sz_boxed_3589_ = lean_unbox_usize(v_sz_3586_);
lean_dec(v_sz_3586_);
v_i_boxed_3590_ = lean_unbox_usize(v_i_3587_);
lean_dec(v_i_3587_);
v_res_3591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3589_, v_i_boxed_3590_, v_bs_3588_);
return v_res_3591_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3592_, lean_object* v___x_3593_, lean_object* v_a_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_){
_start:
{
lean_object* v___x_30400__overap_3600_; lean_object* v___x_3601_; 
v___x_30400__overap_3600_ = l_instInhabitedOfMonad___redArg(v___x_3592_, v___x_3593_);
lean_inc(v___y_3598_);
lean_inc_ref(v___y_3597_);
lean_inc(v___y_3596_);
lean_inc_ref(v___y_3595_);
v___x_3601_ = lean_apply_5(v___x_30400__overap_3600_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, lean_box(0));
return v___x_3601_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3592_ = stack[0].m_obj;
lean_object* v___x_3593_ = stack[1].m_obj;
lean_object* v_a_3594_ = stack[2].m_obj;
lean_object* v___y_3595_ = stack[3].m_obj;
lean_object* v___y_3596_ = stack[4].m_obj;
lean_object* v___y_3597_ = stack[5].m_obj;
lean_object* v___y_3598_ = stack[6].m_obj;
lean_object* v_res_3602_;
v_res_3602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3592_, v___x_3593_, v_a_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
stack->m_obj
 = v_res_3602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3603_, lean_object* v___x_3604_, lean_object* v_a_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3603_, v___x_3604_, v_a_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec_ref(v_a_3605_);
return v_res_3611_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_instMonadEIO___redArg();
return v___x_3612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3614_ = l_StateRefT_x27_instMonad___redArg(v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3619_, lean_object* v_declInfos_3620_, lean_object* v_k_3621_, lean_object* v_kind_3622_, lean_object* v_b_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
uint8_t v_kind_boxed_3629_; lean_object* v_res_3630_; 
v_kind_boxed_3629_ = lean_unbox(v_kind_3622_);
v_res_3630_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3619_, v_declInfos_3620_, v_k_3621_, v_kind_boxed_3629_, v_b_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
return v_res_3630_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3631_, lean_object* v_declInfos_3632_, lean_object* v_k_3633_, uint8_t v_kind_3634_, lean_object* v_name_3635_, uint8_t v_bi_3636_, lean_object* v_type_3637_, uint8_t v_kind_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v___x_3644_; lean_object* v___f_3645_; lean_object* v___x_3646_; 
v___x_3644_ = lean_box(v_kind_3634_);
v___f_3645_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3645_, 0, v_acc_3631_);
lean_closure_set(v___f_3645_, 1, v_declInfos_3632_);
lean_closure_set(v___f_3645_, 2, v_k_3633_);
lean_closure_set(v___f_3645_, 3, v___x_3644_);
v___x_3646_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3635_, v_bi_3636_, v_type_3637_, v___f_3645_, v_kind_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
else
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3662_; 
v_a_3655_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3662_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3662_ == 0)
{
v___x_3657_ = v___x_3646_;
v_isShared_3658_ = v_isSharedCheck_3662_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3646_);
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
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_3631_ = stack[0].m_obj;
lean_object* v_declInfos_3632_ = stack[1].m_obj;
lean_object* v_k_3633_ = stack[2].m_obj;
uint8_t v_kind_3634_ = stack[3].m_num;
lean_object* v_name_3635_ = stack[4].m_obj;
uint8_t v_bi_3636_ = stack[5].m_num;
lean_object* v_type_3637_ = stack[6].m_obj;
uint8_t v_kind_3638_ = stack[7].m_num;
lean_object* v___y_3639_ = stack[8].m_obj;
lean_object* v___y_3640_ = stack[9].m_obj;
lean_object* v___y_3641_ = stack[10].m_obj;
lean_object* v___y_3642_ = stack[11].m_obj;
lean_object* v_res_3663_;
v_res_3663_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3631_, v_declInfos_3632_, v_k_3633_, v_kind_3634_, v_name_3635_, v_bi_3636_, v_type_3637_, v_kind_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
stack->m_obj
 = v_res_3663_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3664_, lean_object* v_k_3665_, uint8_t v_kind_3666_, lean_object* v_acc_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; lean_object* v_toApplicative_3674_; lean_object* v_toFunctor_3675_; lean_object* v_toSeq_3676_; lean_object* v_toSeqLeft_3677_; lean_object* v_toSeqRight_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___f_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v___f_3684_; lean_object* v___f_3685_; lean_object* v___f_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v_toApplicative_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3746_; 
v___x_3673_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3674_ = lean_ctor_get(v___x_3673_, 0);
v_toFunctor_3675_ = lean_ctor_get(v_toApplicative_3674_, 0);
v_toSeq_3676_ = lean_ctor_get(v_toApplicative_3674_, 2);
v_toSeqLeft_3677_ = lean_ctor_get(v_toApplicative_3674_, 3);
v_toSeqRight_3678_ = lean_ctor_get(v_toApplicative_3674_, 4);
v___f_3679_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3680_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3675_, 2);
v___f_3681_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3681_, 0, v_toFunctor_3675_);
v___f_3682_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3682_, 0, v_toFunctor_3675_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___f_3681_);
lean_ctor_set(v___x_3683_, 1, v___f_3682_);
lean_inc(v_toSeqRight_3678_);
v___f_3684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3684_, 0, v_toSeqRight_3678_);
lean_inc(v_toSeqLeft_3677_);
v___f_3685_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3685_, 0, v_toSeqLeft_3677_);
lean_inc(v_toSeq_3676_);
v___f_3686_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3686_, 0, v_toSeq_3676_);
v___x_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3683_);
lean_ctor_set(v___x_3687_, 1, v___f_3679_);
lean_ctor_set(v___x_3687_, 2, v___f_3686_);
lean_ctor_set(v___x_3687_, 3, v___f_3685_);
lean_ctor_set(v___x_3687_, 4, v___f_3684_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v___f_3680_);
v___x_3689_ = l_StateRefT_x27_instMonad___redArg(v___x_3688_);
v_toApplicative_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v___x_3689_, 1);
lean_dec(v_unused_3747_);
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3746_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_toApplicative_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3746_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v_toFunctor_3694_; lean_object* v_toSeq_3695_; lean_object* v_toSeqLeft_3696_; lean_object* v_toSeqRight_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3744_; 
v_toFunctor_3694_ = lean_ctor_get(v_toApplicative_3690_, 0);
v_toSeq_3695_ = lean_ctor_get(v_toApplicative_3690_, 2);
v_toSeqLeft_3696_ = lean_ctor_get(v_toApplicative_3690_, 3);
v_toSeqRight_3697_ = lean_ctor_get(v_toApplicative_3690_, 4);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_toApplicative_3690_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; 
v_unused_3745_ = lean_ctor_get(v_toApplicative_3690_, 1);
lean_dec(v_unused_3745_);
v___x_3699_ = v_toApplicative_3690_;
v_isShared_3700_ = v_isSharedCheck_3744_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_toSeqRight_3697_);
lean_inc(v_toSeqLeft_3696_);
lean_inc(v_toSeq_3695_);
lean_inc(v_toFunctor_3694_);
lean_dec(v_toApplicative_3690_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3744_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___f_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___x_3710_; 
v___f_3701_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3702_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3694_);
v___f_3703_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3703_, 0, v_toFunctor_3694_);
v___f_3704_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3704_, 0, v_toFunctor_3694_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___f_3703_);
lean_ctor_set(v___x_3705_, 1, v___f_3704_);
v___f_3706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3706_, 0, v_toSeqRight_3697_);
v___f_3707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3707_, 0, v_toSeqLeft_3696_);
v___f_3708_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3708_, 0, v_toSeq_3695_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v___f_3706_);
lean_ctor_set(v___x_3699_, 3, v___f_3707_);
lean_ctor_set(v___x_3699_, 2, v___f_3708_);
lean_ctor_set(v___x_3699_, 1, v___f_3701_);
lean_ctor_set(v___x_3699_, 0, v___x_3705_);
v___x_3710_ = v___x_3699_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3743_, 1, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3743_, 2, v___f_3708_);
lean_ctor_set(v_reuseFailAlloc_3743_, 3, v___f_3707_);
lean_ctor_set(v_reuseFailAlloc_3743_, 4, v___f_3706_);
v___x_3710_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 1, v___f_3702_);
lean_ctor_set(v___x_3692_, 0, v___x_3710_);
v___x_3712_ = v___x_3692_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v___f_3702_);
v___x_3712_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = lean_array_get_size(v_acc_3667_);
v___x_3714_ = lean_array_get_size(v_declInfos_3664_);
v___x_3715_ = lean_nat_dec_lt(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_dec_ref(v___x_3712_);
lean_dec_ref(v_declInfos_3664_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
lean_inc(v___y_3669_);
lean_inc_ref(v___y_3668_);
v___x_3716_ = lean_apply_6(v_k_3665_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, lean_box(0));
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___f_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v_snd_3726_; lean_object* v_fst_3727_; lean_object* v_fst_3728_; lean_object* v_snd_3729_; lean_object* v___x_3730_; 
v___x_3717_ = lean_box(0);
v___x_3718_ = 0;
v___x_3719_ = l_Lean_instInhabitedExpr;
v___f_3720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3720_, 0, v___x_3712_);
lean_closure_set(v___f_3720_, 1, v___x_3719_);
v___f_3721_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3721_, 0, v___f_3720_);
v___x_3722_ = lean_box(v___x_3718_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___f_3721_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3717_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_array_get(v___x_3724_, v_declInfos_3664_, v___x_3713_);
lean_dec_ref_known(v___x_3724_, 2);
v_snd_3726_ = lean_ctor_get(v___x_3725_, 1);
lean_inc(v_snd_3726_);
v_fst_3727_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_fst_3727_);
lean_dec(v___x_3725_);
v_fst_3728_ = lean_ctor_get(v_snd_3726_, 0);
lean_inc(v_fst_3728_);
v_snd_3729_ = lean_ctor_get(v_snd_3726_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_snd_3726_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
lean_inc(v___y_3669_);
lean_inc_ref(v___y_3668_);
lean_inc_ref(v_acc_3667_);
v___x_3730_ = lean_apply_6(v_snd_3729_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, lean_box(0));
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
lean_inc(v_a_3731_);
lean_dec_ref_known(v___x_3730_, 1);
v___x_3732_ = lean_unbox(v_fst_3728_);
lean_dec(v_fst_3728_);
v___x_3733_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3667_, v_declInfos_3664_, v_k_3665_, v_kind_3666_, v_fst_3727_, v___x_3732_, v_a_3731_, v_kind_3666_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3733_;
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_fst_3728_);
lean_dec(v_fst_3727_);
lean_dec_ref(v_acc_3667_);
lean_dec_ref(v_k_3665_);
lean_dec_ref(v_declInfos_3664_);
v_a_3734_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3730_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3730_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
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
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3664_ = stack[0].m_obj;
lean_object* v_k_3665_ = stack[1].m_obj;
uint8_t v_kind_3666_ = stack[2].m_num;
lean_object* v_acc_3667_ = stack[3].m_obj;
lean_object* v___y_3668_ = stack[4].m_obj;
lean_object* v___y_3669_ = stack[5].m_obj;
lean_object* v___y_3670_ = stack[6].m_obj;
lean_object* v___y_3671_ = stack[7].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3664_, v_k_3665_, v_kind_3666_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
stack->m_obj
 = v_res_3748_;
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3749_, lean_object* v_declInfos_3750_, lean_object* v_k_3751_, uint8_t v_kind_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_array_push(v_acc_3749_, v_b_3753_);
v___x_3760_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3750_, v_k_3751_, v_kind_3752_, v___x_3759_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3760_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_3749_ = stack[0].m_obj;
lean_object* v_declInfos_3750_ = stack[1].m_obj;
lean_object* v_k_3751_ = stack[2].m_obj;
uint8_t v_kind_3752_ = stack[3].m_num;
lean_object* v_b_3753_ = stack[4].m_obj;
lean_object* v___y_3754_ = stack[5].m_obj;
lean_object* v___y_3755_ = stack[6].m_obj;
lean_object* v___y_3756_ = stack[7].m_obj;
lean_object* v___y_3757_ = stack[8].m_obj;
lean_object* v_res_3761_;
v_res_3761_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3749_, v_declInfos_3750_, v_k_3751_, v_kind_3752_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
stack->m_obj
 = v_res_3761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3762_, lean_object* v_declInfos_3763_, lean_object* v_k_3764_, lean_object* v_kind_3765_, lean_object* v_name_3766_, lean_object* v_bi_3767_, lean_object* v_type_3768_, lean_object* v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v_kind_boxed_3775_; uint8_t v_bi_boxed_3776_; uint8_t v_kind_boxed_3777_; lean_object* v_res_3778_; 
v_kind_boxed_3775_ = lean_unbox(v_kind_3765_);
v_bi_boxed_3776_ = lean_unbox(v_bi_3767_);
v_kind_boxed_3777_ = lean_unbox(v_kind_3769_);
v_res_3778_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3762_, v_declInfos_3763_, v_k_3764_, v_kind_boxed_3775_, v_name_3766_, v_bi_boxed_3776_, v_type_3768_, v_kind_boxed_3777_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3779_, lean_object* v_k_3780_, lean_object* v_kind_3781_, lean_object* v_acc_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
uint8_t v_kind_boxed_3788_; lean_object* v_res_3789_; 
v_kind_boxed_3788_ = lean_unbox(v_kind_3781_);
v_res_3789_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3779_, v_k_3780_, v_kind_boxed_3788_, v_acc_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3789_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3790_, lean_object* v_k_3791_, uint8_t v_kind_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3790_, v_k_3791_, v_kind_3792_, v___x_3798_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3799_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3790_ = stack[0].m_obj;
lean_object* v_k_3791_ = stack[1].m_obj;
uint8_t v_kind_3792_ = stack[2].m_num;
lean_object* v___y_3793_ = stack[3].m_obj;
lean_object* v___y_3794_ = stack[4].m_obj;
lean_object* v___y_3795_ = stack[5].m_obj;
lean_object* v___y_3796_ = stack[6].m_obj;
lean_object* v_res_3800_;
v_res_3800_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3790_, v_k_3791_, v_kind_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
stack->m_obj
 = v_res_3800_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3801_, lean_object* v_k_3802_, lean_object* v_kind_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
uint8_t v_kind_boxed_3809_; lean_object* v_res_3810_; 
v_kind_boxed_3809_ = lean_unbox(v_kind_3803_);
v_res_3810_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3801_, v_k_3802_, v_kind_boxed_3809_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
return v_res_3810_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3811_, lean_object* v_k_3812_, uint8_t v_kind_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_sz_3819_ = lean_array_size(v_declInfos_3811_);
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3819_, v___x_3820_, v_declInfos_3811_);
v___x_3822_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3821_, v_k_3812_, v_kind_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
return v___x_3822_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3811_ = stack[0].m_obj;
lean_object* v_k_3812_ = stack[1].m_obj;
uint8_t v_kind_3813_ = stack[2].m_num;
lean_object* v___y_3814_ = stack[3].m_obj;
lean_object* v___y_3815_ = stack[4].m_obj;
lean_object* v___y_3816_ = stack[5].m_obj;
lean_object* v___y_3817_ = stack[6].m_obj;
lean_object* v_res_3823_;
v_res_3823_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3811_, v_k_3812_, v_kind_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
stack->m_obj
 = v_res_3823_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3824_, lean_object* v_k_3825_, lean_object* v_kind_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
uint8_t v_kind_boxed_3832_; lean_object* v_res_3833_; 
v_kind_boxed_3832_ = lean_unbox(v_kind_3826_);
v_res_3833_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3824_, v_k_3825_, v_kind_boxed_3832_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
return v_res_3833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3835_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3836_ = lean_unsigned_to_nat(4u);
v___x_3837_ = lean_unsigned_to_nat(202u);
v___x_3838_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3839_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3840_ = l_mkPanicMessageWithDecl(v___x_3839_, v___x_3838_, v___x_3837_, v___x_3836_, v___x_3835_);
return v___x_3840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3847_ = l_Lean_stringToMessageData(v___x_3846_);
return v___x_3847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3850_ = l_Lean_stringToMessageData(v___x_3849_);
return v___x_3850_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3851_, lean_object* v_numMotives_3852_, lean_object* v_numMinors_3853_, lean_object* v___x_3854_, lean_object* v_all_3855_, lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v_head_3858_, lean_object* v_tail_3859_, lean_object* v_recName_3860_, lean_object* v_brecOnGoName_3861_, lean_object* v_levelParams_3862_, lean_object* v_brecOnName_3863_, lean_object* v_brecOnEqName_3864_, lean_object* v_type_3865_, lean_object* v_refArgs_3866_, lean_object* v_refBody_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; 
v___x_3873_ = lean_nat_add(v_nParams_3851_, v_numMotives_3852_);
v___x_3874_ = lean_nat_add(v___x_3873_, v_numMinors_3853_);
v___x_3875_ = lean_array_get_size(v_refArgs_3866_);
v___x_3876_ = lean_nat_dec_lt(v___x_3874_, v___x_3875_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_dec(v___x_3874_);
lean_dec(v___x_3873_);
lean_dec_ref(v_refArgs_3866_);
lean_dec_ref(v_type_3865_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3856_);
lean_dec_ref(v_all_3855_);
lean_dec(v___x_3854_);
lean_dec(v_nParams_3851_);
v___x_3877_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3878_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3877_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3851_);
lean_inc_ref_n(v_refArgs_3866_, 2);
v___x_3880_ = l_Array_toSubarray___redArg(v_refArgs_3866_, v___x_3879_, v_nParams_3851_);
lean_inc(v___x_3873_);
v___x_3881_ = l_Array_toSubarray___redArg(v_refArgs_3866_, v_nParams_3851_, v___x_3873_);
v___x_3882_ = l_Subarray_copy___redArg(v___x_3881_);
v___x_3883_ = l_Lean_Expr_getAppFn(v_refBody_3867_);
v___x_3884_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3882_, v___x_3883_);
lean_dec_ref(v___x_3883_);
if (lean_obj_tag(v___x_3884_) == 1)
{
lean_object* v_val_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec_ref(v_type_3865_);
v_val_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_val_3885_);
lean_dec_ref_known(v___x_3884_, 1);
lean_inc_n(v___x_3874_, 2);
lean_inc_ref_n(v_refArgs_3866_, 2);
v___x_3886_ = l_Array_toSubarray___redArg(v_refArgs_3866_, v___x_3873_, v___x_3874_);
v___x_3887_ = l_Subarray_copy___redArg(v___x_3880_);
v___x_3888_ = l_Subarray_copy___redArg(v___x_3886_);
v___x_3889_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3882_);
lean_inc_ref(v___x_3887_);
lean_inc(v___x_3854_);
v___f_3890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3890_, 0, v___x_3854_);
lean_closure_set(v___f_3890_, 1, v___x_3887_);
lean_closure_set(v___f_3890_, 2, v___x_3882_);
lean_closure_set(v___f_3890_, 3, v_all_3855_);
lean_closure_set(v___f_3890_, 4, v___x_3856_);
lean_closure_set(v___f_3890_, 5, v___x_3879_);
lean_closure_set(v___f_3890_, 6, v___x_3889_);
v___x_3891_ = lean_nat_sub(v___x_3875_, v___x_3889_);
lean_inc(v___x_3891_);
v___x_3892_ = l_Array_toSubarray___redArg(v_refArgs_3866_, v___x_3874_, v___x_3891_);
v___x_3893_ = l_Subarray_copy___redArg(v___x_3892_);
v___x_3894_ = lean_array_get(v___x_3857_, v_refArgs_3866_, v___x_3891_);
lean_dec(v___x_3891_);
lean_dec_ref(v_refArgs_3866_);
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
lean_inc(v___x_3894_);
v___x_3895_ = lean_infer_type(v___x_3894_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
lean_inc(v___y_3871_);
lean_inc_ref(v___y_3870_);
lean_inc(v___y_3869_);
lean_inc_ref(v___y_3868_);
v___x_3897_ = lean_infer_type(v_a_3896_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3898_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
if (lean_obj_tag(v_a_3900_) == 1)
{
lean_object* v_val_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___f_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; size_t v_sz_3914_; size_t v___x_3915_; lean_object* v___x_3916_; 
v_val_3901_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v_a_3900_, 1);
v___x_3902_ = l_Lean_mkLevelMax(v_val_3901_, v_head_3858_);
v___x_3903_ = lean_array_get_size(v___x_3882_);
v___x_3904_ = l_Array_ofFn___redArg(v___x_3903_, v___f_3890_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3906_ = lean_array_get_size(v___x_3904_);
lean_inc_ref(v___x_3904_);
v___x_3907_ = l_Array_toSubarray___redArg(v___x_3904_, v___x_3879_, v___x_3906_);
v___x_3908_ = lean_box(v___x_3876_);
lean_inc(v___x_3874_);
lean_inc_ref(v___x_3882_);
lean_inc_ref(v___x_3907_);
v___f_3909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3909_, 0, v___x_3902_);
lean_closure_set(v___f_3909_, 1, v_tail_3859_);
lean_closure_set(v___f_3909_, 2, v_recName_3860_);
lean_closure_set(v___f_3909_, 3, v___x_3887_);
lean_closure_set(v___f_3909_, 4, v___x_3907_);
lean_closure_set(v___f_3909_, 5, v___x_3882_);
lean_closure_set(v___f_3909_, 6, v___x_3874_);
lean_closure_set(v___f_3909_, 7, v___x_3875_);
lean_closure_set(v___f_3909_, 8, v___x_3888_);
lean_closure_set(v___f_3909_, 9, v___x_3904_);
lean_closure_set(v___f_3909_, 10, v___x_3893_);
lean_closure_set(v___f_3909_, 11, v___x_3894_);
lean_closure_set(v___f_3909_, 12, v___x_3889_);
lean_closure_set(v___f_3909_, 13, v___x_3857_);
lean_closure_set(v___f_3909_, 14, v_val_3885_);
lean_closure_set(v___f_3909_, 15, v___x_3908_);
lean_closure_set(v___f_3909_, 16, v_brecOnGoName_3861_);
lean_closure_set(v___f_3909_, 17, v_levelParams_3862_);
lean_closure_set(v___f_3909_, 18, v___x_3854_);
lean_closure_set(v___f_3909_, 19, v_brecOnName_3863_);
lean_closure_set(v___f_3909_, 20, v___x_3879_);
lean_closure_set(v___f_3909_, 21, v_brecOnEqName_3864_);
v___x_3910_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
lean_ctor_set(v___x_3911_, 1, v___x_3903_);
v___x_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3907_);
lean_ctor_set(v___x_3912_, 1, v___x_3911_);
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3905_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v_sz_3914_ = lean_array_size(v___x_3882_);
v___x_3915_ = ((size_t)0ULL);
v___x_3916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3874_, v___x_3875_, v___x_3882_, v_sz_3914_, v___x_3915_, v___x_3913_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec_ref(v___x_3882_);
lean_dec(v___x_3874_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v_fst_3918_; uint8_t v___x_3919_; lean_object* v___x_3920_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v_fst_3918_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_fst_3918_);
lean_dec(v_a_3917_);
v___x_3919_ = 0;
v___x_3920_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3918_, v___f_3909_, v___x_3919_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3920_;
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v___f_3909_);
v_a_3921_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3916_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3916_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec(v_a_3900_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v___f_3890_);
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v___x_3882_);
lean_dec(v___x_3874_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3854_);
v___x_3929_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3930_ = l_Lean_MessageData_ofExpr(v___x_3894_);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3931_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3933_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3934_;
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v___x_3894_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v___f_3890_);
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v___x_3882_);
lean_dec(v___x_3874_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3854_);
v_a_3935_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3899_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3899_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v___x_3894_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v___f_3890_);
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v___x_3882_);
lean_dec(v___x_3874_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3854_);
v_a_3943_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3897_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3897_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v___x_3894_);
lean_dec_ref(v___x_3893_);
lean_dec_ref(v___f_3890_);
lean_dec_ref(v___x_3888_);
lean_dec_ref(v___x_3887_);
lean_dec(v_val_3885_);
lean_dec_ref(v___x_3882_);
lean_dec(v___x_3874_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3854_);
v_a_3951_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3895_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3895_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec(v___x_3884_);
lean_dec_ref(v___x_3880_);
lean_dec(v___x_3874_);
lean_dec(v___x_3873_);
lean_dec_ref(v_refArgs_3866_);
lean_dec(v_brecOnEqName_3864_);
lean_dec(v_brecOnName_3863_);
lean_dec(v_levelParams_3862_);
lean_dec(v_brecOnGoName_3861_);
lean_dec(v_recName_3860_);
lean_dec(v_tail_3859_);
lean_dec(v_head_3858_);
lean_dec_ref(v___x_3857_);
lean_dec(v___x_3856_);
lean_dec_ref(v_all_3855_);
lean_dec(v___x_3854_);
v___x_3959_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3960_ = l_Lean_MessageData_ofExpr(v_type_3865_);
v___x_3961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3959_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3961_);
lean_ctor_set(v___x_3963_, 1, v___x_3962_);
v___x_3964_ = lean_array_to_list(v___x_3882_);
v___x_3965_ = lean_box(0);
v___x_3966_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3964_, v___x_3965_);
v___x_3967_ = l_Lean_MessageData_ofList(v___x_3966_);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3963_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3968_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3969_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_nParams_3851_ = stack[0].m_obj;
lean_object* v_numMotives_3852_ = stack[1].m_obj;
lean_object* v_numMinors_3853_ = stack[2].m_obj;
lean_object* v___x_3854_ = stack[3].m_obj;
lean_object* v_all_3855_ = stack[4].m_obj;
lean_object* v___x_3856_ = stack[5].m_obj;
lean_object* v___x_3857_ = stack[6].m_obj;
lean_object* v_head_3858_ = stack[7].m_obj;
lean_object* v_tail_3859_ = stack[8].m_obj;
lean_object* v_recName_3860_ = stack[9].m_obj;
lean_object* v_brecOnGoName_3861_ = stack[10].m_obj;
lean_object* v_levelParams_3862_ = stack[11].m_obj;
lean_object* v_brecOnName_3863_ = stack[12].m_obj;
lean_object* v_brecOnEqName_3864_ = stack[13].m_obj;
lean_object* v_type_3865_ = stack[14].m_obj;
lean_object* v_refArgs_3866_ = stack[15].m_obj;
lean_object* v_refBody_3867_ = stack[16].m_obj;
lean_object* v___y_3868_ = stack[17].m_obj;
lean_object* v___y_3869_ = stack[18].m_obj;
lean_object* v___y_3870_ = stack[19].m_obj;
lean_object* v___y_3871_ = stack[20].m_obj;
lean_object* v_res_3970_;
v_res_3970_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3851_, v_numMotives_3852_, v_numMinors_3853_, v___x_3854_, v_all_3855_, v___x_3856_, v___x_3857_, v_head_3858_, v_tail_3859_, v_recName_3860_, v_brecOnGoName_3861_, v_levelParams_3862_, v_brecOnName_3863_, v_brecOnEqName_3864_, v_type_3865_, v_refArgs_3866_, v_refBody_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
stack->m_obj
 = v_res_3970_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3971_ = _args[0];
lean_object* v_numMotives_3972_ = _args[1];
lean_object* v_numMinors_3973_ = _args[2];
lean_object* v___x_3974_ = _args[3];
lean_object* v_all_3975_ = _args[4];
lean_object* v___x_3976_ = _args[5];
lean_object* v___x_3977_ = _args[6];
lean_object* v_head_3978_ = _args[7];
lean_object* v_tail_3979_ = _args[8];
lean_object* v_recName_3980_ = _args[9];
lean_object* v_brecOnGoName_3981_ = _args[10];
lean_object* v_levelParams_3982_ = _args[11];
lean_object* v_brecOnName_3983_ = _args[12];
lean_object* v_brecOnEqName_3984_ = _args[13];
lean_object* v_type_3985_ = _args[14];
lean_object* v_refArgs_3986_ = _args[15];
lean_object* v_refBody_3987_ = _args[16];
lean_object* v___y_3988_ = _args[17];
lean_object* v___y_3989_ = _args[18];
lean_object* v___y_3990_ = _args[19];
lean_object* v___y_3991_ = _args[20];
lean_object* v___y_3992_ = _args[21];
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3971_, v_numMotives_3972_, v_numMinors_3973_, v___x_3974_, v_all_3975_, v___x_3976_, v___x_3977_, v_head_3978_, v_tail_3979_, v_recName_3980_, v_brecOnGoName_3981_, v_levelParams_3982_, v_brecOnName_3983_, v_brecOnEqName_3984_, v_type_3985_, v_refArgs_3986_, v_refBody_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec_ref(v_refBody_3987_);
lean_dec(v_numMinors_3973_);
lean_dec(v_numMotives_3972_);
return v_res_3993_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3996_, lean_object* v_nParams_3997_, lean_object* v_all_3998_, lean_object* v_brecOnName_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_brecOnGoName_4008_; lean_object* v___x_4009_; lean_object* v_brecOnEqName_4010_; lean_object* v___x_4011_; 
v___x_4005_ = l_Lean_instInhabitedExpr;
v___x_4006_ = lean_box(0);
v___x_4007_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3999_, 2);
v_brecOnGoName_4008_ = l_Lean_Name_str___override(v_brecOnName_3999_, v___x_4007_);
v___x_4009_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_4010_ = l_Lean_Name_str___override(v_brecOnName_3999_, v___x_4009_);
lean_inc(v_recName_3996_);
v___x_4011_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3996_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4039_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4014_ = v___x_4011_;
v_isShared_4015_ = v_isSharedCheck_4039_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4011_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4039_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
if (lean_obj_tag(v_a_4012_) == 7)
{
lean_object* v_val_4016_; lean_object* v_toConstantVal_4017_; lean_object* v_numMotives_4018_; lean_object* v_numMinors_4019_; lean_object* v_levelParams_4020_; lean_object* v_type_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_4014_);
v_val_4016_ = lean_ctor_get(v_a_4012_, 0);
lean_inc_ref(v_val_4016_);
lean_dec_ref_known(v_a_4012_, 1);
v_toConstantVal_4017_ = lean_ctor_get(v_val_4016_, 0);
lean_inc_ref(v_toConstantVal_4017_);
v_numMotives_4018_ = lean_ctor_get(v_val_4016_, 4);
lean_inc(v_numMotives_4018_);
v_numMinors_4019_ = lean_ctor_get(v_val_4016_, 5);
lean_inc(v_numMinors_4019_);
lean_dec_ref(v_val_4016_);
v_levelParams_4020_ = lean_ctor_get(v_toConstantVal_4017_, 1);
lean_inc_n(v_levelParams_4020_, 2);
v_type_4021_ = lean_ctor_get(v_toConstantVal_4017_, 2);
lean_inc_ref(v_type_4021_);
lean_dec_ref(v_toConstantVal_4017_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_4020_, v___x_4022_);
if (lean_obj_tag(v___x_4023_) == 1)
{
lean_object* v_head_4024_; lean_object* v_tail_4025_; lean_object* v___f_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; 
v_head_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_head_4024_);
v_tail_4025_ = lean_ctor_get(v___x_4023_, 1);
lean_inc(v_tail_4025_);
lean_inc_ref(v_type_4021_);
v___f_4026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_4026_, 0, v_nParams_3997_);
lean_closure_set(v___f_4026_, 1, v_numMotives_4018_);
lean_closure_set(v___f_4026_, 2, v_numMinors_4019_);
lean_closure_set(v___f_4026_, 3, v___x_4023_);
lean_closure_set(v___f_4026_, 4, v_all_3998_);
lean_closure_set(v___f_4026_, 5, v___x_4006_);
lean_closure_set(v___f_4026_, 6, v___x_4005_);
lean_closure_set(v___f_4026_, 7, v_head_4024_);
lean_closure_set(v___f_4026_, 8, v_tail_4025_);
lean_closure_set(v___f_4026_, 9, v_recName_3996_);
lean_closure_set(v___f_4026_, 10, v_brecOnGoName_4008_);
lean_closure_set(v___f_4026_, 11, v_levelParams_4020_);
lean_closure_set(v___f_4026_, 12, v_brecOnName_3999_);
lean_closure_set(v___f_4026_, 13, v_brecOnEqName_4010_);
lean_closure_set(v___f_4026_, 14, v_type_4021_);
v___x_4027_ = 0;
v___x_4028_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_4021_, v___f_4026_, v___x_4027_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
return v___x_4028_;
}
else
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
lean_dec(v___x_4023_);
lean_dec_ref(v_type_4021_);
lean_dec(v_levelParams_4020_);
lean_dec(v_numMinors_4019_);
lean_dec(v_numMotives_4018_);
lean_dec(v_brecOnEqName_4010_);
lean_dec(v_brecOnGoName_4008_);
lean_dec(v_brecOnName_3999_);
lean_dec_ref(v_all_3998_);
lean_dec(v_nParams_3997_);
v___x_4029_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_4030_ = l_Lean_MessageData_ofName(v_recName_3996_);
v___x_4031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4029_);
lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_4033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4031_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
v___x_4034_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_4033_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
return v___x_4034_;
}
}
else
{
lean_object* v___x_4035_; lean_object* v___x_4037_; 
lean_dec(v_a_4012_);
lean_dec(v_brecOnEqName_4010_);
lean_dec(v_brecOnGoName_4008_);
lean_dec(v_brecOnName_3999_);
lean_dec_ref(v_all_3998_);
lean_dec(v_nParams_3997_);
lean_dec(v_recName_3996_);
v___x_4035_ = lean_box(0);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4035_);
v___x_4037_ = v___x_4014_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4035_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
lean_dec(v_brecOnEqName_4010_);
lean_dec(v_brecOnGoName_4008_);
lean_dec(v_brecOnName_3999_);
lean_dec_ref(v_all_3998_);
lean_dec(v_nParams_3997_);
lean_dec(v_recName_3996_);
v_a_4040_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4011_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4011_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_recName_3996_ = stack[0].m_obj;
lean_object* v_nParams_3997_ = stack[1].m_obj;
lean_object* v_all_3998_ = stack[2].m_obj;
lean_object* v_brecOnName_3999_ = stack[3].m_obj;
lean_object* v_a_4000_ = stack[4].m_obj;
lean_object* v_a_4001_ = stack[5].m_obj;
lean_object* v_a_4002_ = stack[6].m_obj;
lean_object* v_a_4003_ = stack[7].m_obj;
lean_object* v_res_4048_;
v_res_4048_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3996_, v_nParams_3997_, v_all_3998_, v_brecOnName_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
stack->m_obj
 = v_res_4048_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_4049_, lean_object* v_nParams_4050_, lean_object* v_all_4051_, lean_object* v_brecOnName_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_4049_, v_nParams_4050_, v_all_4051_, v_brecOnName_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
lean_dec(v_a_4056_);
lean_dec_ref(v_a_4055_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
return v_res_4058_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_4059_, lean_object* v___x_4060_, lean_object* v___x_4061_, lean_object* v___x_4062_, lean_object* v___x_4063_, lean_object* v_a_4064_, lean_object* v_b_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
uint8_t v___x_4071_; 
v___x_4071_ = lean_nat_dec_lt(v_a_4064_, v_upperBound_4059_);
if (v___x_4071_ == 0)
{
lean_object* v___x_4072_; 
lean_dec(v_a_4064_);
lean_dec_ref(v___x_4063_);
lean_dec(v___x_4062_);
lean_dec(v___x_4061_);
lean_dec(v___x_4060_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v_b_4065_);
return v___x_4072_;
}
else
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4073_ = lean_box(0);
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = lean_nat_add(v_a_4064_, v___x_4074_);
lean_dec(v_a_4064_);
lean_inc_n(v___x_4075_, 2);
lean_inc(v___x_4060_);
v___x_4076_ = lean_name_append_index_after(v___x_4060_, v___x_4075_);
lean_inc(v___x_4061_);
v___x_4077_ = lean_name_append_index_after(v___x_4061_, v___x_4075_);
lean_inc_ref(v___x_4063_);
lean_inc(v___x_4062_);
v___x_4078_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4076_, v___x_4062_, v___x_4063_, v___x_4077_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_dec_ref_known(v___x_4078_, 1);
v_a_4064_ = v___x_4075_;
v_b_4065_ = v___x_4073_;
goto _start;
}
else
{
lean_dec(v___x_4075_);
lean_dec_ref(v___x_4063_);
lean_dec(v___x_4062_);
lean_dec(v___x_4061_);
lean_dec(v___x_4060_);
return v___x_4078_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4059_ = stack[0].m_obj;
lean_object* v___x_4060_ = stack[1].m_obj;
lean_object* v___x_4061_ = stack[2].m_obj;
lean_object* v___x_4062_ = stack[3].m_obj;
lean_object* v___x_4063_ = stack[4].m_obj;
lean_object* v_a_4064_ = stack[5].m_obj;
lean_object* v_b_4065_ = stack[6].m_obj;
lean_object* v___y_4066_ = stack[7].m_obj;
lean_object* v___y_4067_ = stack[8].m_obj;
lean_object* v___y_4068_ = stack[9].m_obj;
lean_object* v___y_4069_ = stack[10].m_obj;
lean_object* v_res_4080_;
v_res_4080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v_a_4064_, v_b_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
stack->m_obj
 = v_res_4080_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_4081_, lean_object* v___x_4082_, lean_object* v___x_4083_, lean_object* v___x_4084_, lean_object* v___x_4085_, lean_object* v_a_4086_, lean_object* v_b_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4081_, v___x_4082_, v___x_4083_, v___x_4084_, v___x_4085_, v_a_4086_, v_b_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v_upperBound_4081_);
return v_res_4093_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4099_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_4100_ = l_Lean_Name_append(v___x_4099_, v___x_4098_);
return v___x_4100_;
}
}
lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_){
_start:
{
lean_object* v_toCold_4107_; lean_object* v_options_4108_; lean_object* v_inheritedTraceOptions_4109_; uint8_t v_hasTrace_4110_; lean_object* v___x_4111_; 
v_toCold_4107_ = lean_ctor_get(v_a_4104_, 0);
v_options_4108_ = lean_ctor_get(v_toCold_4107_, 2);
v_inheritedTraceOptions_4109_ = lean_ctor_get(v_toCold_4107_, 11);
v_hasTrace_4110_ = lean_ctor_get_uint8(v_options_4108_, sizeof(void*)*1);
v___x_4111_ = lean_box(0);
if (v_hasTrace_4110_ == 0)
{
lean_object* v___x_4112_; 
lean_inc(v_indName_4101_);
v___x_4112_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4177_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4177_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4177_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
if (lean_obj_tag(v_a_4113_) == 5)
{
lean_object* v_val_4117_; uint8_t v_isRec_4118_; 
v_val_4117_ = lean_ctor_get(v_a_4113_, 0);
lean_inc_ref(v_val_4117_);
lean_dec_ref_known(v_a_4113_, 1);
v_isRec_4118_ = lean_ctor_get_uint8(v_val_4117_, sizeof(void*)*6);
if (v_isRec_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4121_; 
lean_dec_ref(v_val_4117_);
lean_dec(v_indName_4101_);
v___x_4119_ = lean_box(0);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4119_);
v___x_4121_ = v___x_4115_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
else
{
lean_object* v_toConstantVal_4123_; lean_object* v_numParams_4124_; lean_object* v_all_4125_; lean_object* v_numNested_4126_; lean_object* v_type_4127_; lean_object* v___x_4128_; 
lean_del_object(v___x_4115_);
v_toConstantVal_4123_ = lean_ctor_get(v_val_4117_, 0);
lean_inc_ref(v_toConstantVal_4123_);
v_numParams_4124_ = lean_ctor_get(v_val_4117_, 1);
lean_inc(v_numParams_4124_);
v_all_4125_ = lean_ctor_get(v_val_4117_, 3);
lean_inc(v_all_4125_);
v_numNested_4126_ = lean_ctor_get(v_val_4117_, 5);
lean_inc(v_numNested_4126_);
lean_dec_ref(v_val_4117_);
v_type_4127_ = lean_ctor_get(v_toConstantVal_4123_, 2);
lean_inc_ref(v_type_4127_);
lean_dec_ref(v_toConstantVal_4123_);
v___x_4128_ = l_Lean_Meta_isPropFormerType(v_type_4127_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4164_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4164_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4164_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_unbox(v_a_4129_);
lean_dec(v_a_4129_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
lean_del_object(v___x_4131_);
lean_inc_n(v_indName_4101_, 2);
v___x_4134_ = l_Lean_mkRecName(v_indName_4101_);
v___x_4135_ = l_Lean_mkBRecOnName(v_indName_4101_);
lean_inc(v_all_4125_);
v___x_4136_ = lean_array_mk(v_all_4125_);
lean_inc(v___x_4135_);
lean_inc_ref(v___x_4136_);
lean_inc(v_numParams_4124_);
lean_inc(v___x_4134_);
v___x_4137_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4134_, v_numParams_4124_, v___x_4136_, v___x_4135_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4158_; 
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4158_ == 0)
{
lean_object* v_unused_4159_; 
v_unused_4159_ = lean_ctor_get(v___x_4137_, 0);
lean_dec(v_unused_4159_);
v___x_4139_ = v___x_4137_;
v_isShared_4140_ = v_isSharedCheck_4158_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v___x_4137_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4158_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v___x_4141_ = lean_unsigned_to_nat(0u);
v___x_4142_ = l_List_get_x21Internal___redArg(v___x_4111_, v_all_4125_, v___x_4141_);
lean_dec(v_all_4125_);
v___x_4143_ = lean_name_eq(v___x_4142_, v_indName_4101_);
lean_dec(v_indName_4101_);
lean_dec(v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4146_; 
lean_dec_ref(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v_numNested_4126_);
lean_dec(v_numParams_4124_);
v___x_4144_ = lean_box(0);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4144_);
v___x_4146_ = v___x_4139_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_del_object(v___x_4139_);
v___x_4148_ = lean_box(0);
v___x_4149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4126_, v___x_4134_, v___x_4135_, v_numParams_4124_, v___x_4136_, v___x_4141_, v___x_4148_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_numNested_4126_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_isSharedCheck_4156_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v___x_4149_, 0);
lean_dec(v_unused_4157_);
v___x_4151_ = v___x_4149_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_dec(v___x_4149_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4148_);
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4148_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
return v___x_4154_;
}
}
}
else
{
return v___x_4149_;
}
}
}
}
else
{
lean_dec_ref(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_4101_);
return v___x_4137_;
}
}
else
{
lean_object* v___x_4160_; lean_object* v___x_4162_; 
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_4101_);
v___x_4160_ = lean_box(0);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v___x_4160_);
v___x_4162_ = v___x_4131_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_4101_);
v_a_4165_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4128_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4128_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4175_; 
lean_dec(v_a_4113_);
lean_dec(v_indName_4101_);
v___x_4173_ = lean_box(0);
if (v_isShared_4116_ == 0)
{
lean_ctor_set(v___x_4115_, 0, v___x_4173_);
v___x_4175_ = v___x_4115_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec(v_indName_4101_);
v_a_4178_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4112_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4112_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
else
{
lean_object* v___f_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v_a_4209_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v_a_4214_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v_a_4219_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v_a_4231_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v_a_4236_; 
lean_inc(v_indName_4101_);
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4186_, 0, v_indName_4101_);
v___x_4187_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4188_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4189_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4190_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4108_, v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4305_ = l_Lean_trace_profiler;
v___x_4306_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4108_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; 
lean_dec_ref(v___f_4186_);
lean_inc(v_indName_4101_);
v___x_4307_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4372_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4372_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4372_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
if (lean_obj_tag(v_a_4308_) == 5)
{
lean_object* v_val_4312_; uint8_t v_isRec_4313_; 
v_val_4312_ = lean_ctor_get(v_a_4308_, 0);
lean_inc_ref(v_val_4312_);
lean_dec_ref_known(v_a_4308_, 1);
v_isRec_4313_ = lean_ctor_get_uint8(v_val_4312_, sizeof(void*)*6);
if (v_isRec_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
lean_dec_ref(v_val_4312_);
lean_dec(v_indName_4101_);
v___x_4314_ = lean_box(0);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v___x_4314_);
v___x_4316_ = v___x_4310_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
else
{
lean_object* v_toConstantVal_4318_; lean_object* v_numParams_4319_; lean_object* v_all_4320_; lean_object* v_numNested_4321_; lean_object* v_type_4322_; lean_object* v___x_4323_; 
lean_del_object(v___x_4310_);
v_toConstantVal_4318_ = lean_ctor_get(v_val_4312_, 0);
lean_inc_ref(v_toConstantVal_4318_);
v_numParams_4319_ = lean_ctor_get(v_val_4312_, 1);
lean_inc(v_numParams_4319_);
v_all_4320_ = lean_ctor_get(v_val_4312_, 3);
lean_inc(v_all_4320_);
v_numNested_4321_ = lean_ctor_get(v_val_4312_, 5);
lean_inc(v_numNested_4321_);
lean_dec_ref(v_val_4312_);
v_type_4322_ = lean_ctor_get(v_toConstantVal_4318_, 2);
lean_inc_ref(v_type_4322_);
lean_dec_ref(v_toConstantVal_4318_);
v___x_4323_ = l_Lean_Meta_isPropFormerType(v_type_4322_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4359_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4359_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4359_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
uint8_t v___x_4328_; 
v___x_4328_ = lean_unbox(v_a_4324_);
lean_dec(v_a_4324_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
lean_del_object(v___x_4326_);
lean_inc_n(v_indName_4101_, 2);
v___x_4329_ = l_Lean_mkRecName(v_indName_4101_);
v___x_4330_ = l_Lean_mkBRecOnName(v_indName_4101_);
lean_inc(v_all_4320_);
v___x_4331_ = lean_array_mk(v_all_4320_);
lean_inc(v___x_4330_);
lean_inc_ref(v___x_4331_);
lean_inc(v_numParams_4319_);
lean_inc(v___x_4329_);
v___x_4332_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4329_, v_numParams_4319_, v___x_4331_, v___x_4330_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4353_; 
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v___x_4332_, 0);
lean_dec(v_unused_4354_);
v___x_4334_ = v___x_4332_;
v_isShared_4335_ = v_isSharedCheck_4353_;
goto v_resetjp_4333_;
}
else
{
lean_dec(v___x_4332_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4353_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = l_List_get_x21Internal___redArg(v___x_4111_, v_all_4320_, v___x_4336_);
lean_dec(v_all_4320_);
v___x_4338_ = lean_name_eq(v___x_4337_, v_indName_4101_);
lean_dec(v_indName_4101_);
lean_dec(v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; lean_object* v___x_4341_; 
lean_dec_ref(v___x_4331_);
lean_dec(v___x_4330_);
lean_dec(v___x_4329_);
lean_dec(v_numNested_4321_);
lean_dec(v_numParams_4319_);
v___x_4339_ = lean_box(0);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4339_);
v___x_4341_ = v___x_4334_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
lean_del_object(v___x_4334_);
v___x_4343_ = lean_box(0);
v___x_4344_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4321_, v___x_4329_, v___x_4330_, v_numParams_4319_, v___x_4331_, v___x_4336_, v___x_4343_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_numNested_4321_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4351_ == 0)
{
lean_object* v_unused_4352_; 
v_unused_4352_ = lean_ctor_get(v___x_4344_, 0);
lean_dec(v_unused_4352_);
v___x_4346_ = v___x_4344_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_dec(v___x_4344_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 0, v___x_4343_);
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4343_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
else
{
return v___x_4344_;
}
}
}
}
else
{
lean_dec_ref(v___x_4331_);
lean_dec(v___x_4330_);
lean_dec(v___x_4329_);
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_indName_4101_);
return v___x_4332_;
}
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_indName_4101_);
v___x_4355_ = lean_box(0);
if (v_isShared_4327_ == 0)
{
lean_ctor_set(v___x_4326_, 0, v___x_4355_);
v___x_4357_ = v___x_4326_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4355_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_indName_4101_);
v_a_4360_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4323_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4323_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
else
{
lean_object* v___x_4368_; lean_object* v___x_4370_; 
lean_dec(v_a_4308_);
lean_dec(v_indName_4101_);
v___x_4368_ = lean_box(0);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v___x_4368_);
v___x_4370_ = v___x_4310_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_dec(v_indName_4101_);
v_a_4373_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4307_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4307_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
goto v___jp_4238_;
}
}
else
{
goto v___jp_4238_;
}
v___jp_4191_:
{
lean_object* v___x_4195_; double v___x_4196_; double v___x_4197_; double v___x_4198_; double v___x_4199_; double v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4195_ = lean_io_mono_nanos_now();
v___x_4196_ = lean_float_of_nat(v___y_4193_);
v___x_4197_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4198_ = lean_float_div(v___x_4196_, v___x_4197_);
v___x_4199_ = lean_float_of_nat(v___x_4195_);
v___x_4200_ = lean_float_div(v___x_4199_, v___x_4197_);
v___x_4201_ = lean_box_float(v___x_4198_);
v___x_4202_ = lean_box_float(v___x_4200_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4194_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4187_, v_hasTrace_4110_, v___x_4188_, v_options_4108_, v___x_4190_, v___y_4192_, v___f_4186_, v___x_4204_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
return v___x_4205_;
}
v___jp_4206_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4209_);
v___y_4192_ = v___y_4207_;
v___y_4193_ = v___y_4208_;
v_a_4194_ = v___x_4210_;
goto v___jp_4191_;
}
v___jp_4211_:
{
lean_object* v___x_4215_; 
v___x_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4215_, 0, v_a_4214_);
v___y_4192_ = v___y_4212_;
v___y_4193_ = v___y_4213_;
v_a_4194_ = v___x_4215_;
goto v___jp_4191_;
}
v___jp_4216_:
{
lean_object* v___x_4220_; double v___x_4221_; double v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4220_ = lean_io_get_num_heartbeats();
v___x_4221_ = lean_float_of_nat(v___y_4218_);
v___x_4222_ = lean_float_of_nat(v___x_4220_);
v___x_4223_ = lean_box_float(v___x_4221_);
v___x_4224_ = lean_box_float(v___x_4222_);
v___x_4225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4223_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
v___x_4226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4226_, 0, v_a_4219_);
lean_ctor_set(v___x_4226_, 1, v___x_4225_);
v___x_4227_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4187_, v_hasTrace_4110_, v___x_4188_, v_options_4108_, v___x_4190_, v___y_4217_, v___f_4186_, v___x_4226_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
return v___x_4227_;
}
v___jp_4228_:
{
lean_object* v___x_4232_; 
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v_a_4231_);
v___y_4217_ = v___y_4229_;
v___y_4218_ = v___y_4230_;
v_a_4219_ = v___x_4232_;
goto v___jp_4216_;
}
v___jp_4233_:
{
lean_object* v___x_4237_; 
v___x_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4237_, 0, v_a_4236_);
v___y_4217_ = v___y_4234_;
v___y_4218_ = v___y_4235_;
v_a_4219_ = v___x_4237_;
goto v___jp_4216_;
}
v___jp_4238_:
{
lean_object* v___x_4239_; lean_object* v_a_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v___x_4239_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_4105_);
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref(v___x_4239_);
v___x_4241_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4242_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4108_, v___x_4241_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = lean_io_mono_nanos_now();
lean_inc(v_indName_4101_);
v___x_4244_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
if (lean_obj_tag(v_a_4245_) == 5)
{
lean_object* v_val_4246_; uint8_t v_isRec_4247_; 
v_val_4246_ = lean_ctor_get(v_a_4245_, 0);
lean_inc_ref(v_val_4246_);
lean_dec_ref_known(v_a_4245_, 1);
v_isRec_4247_ = lean_ctor_get_uint8(v_val_4246_, sizeof(void*)*6);
if (v_isRec_4247_ == 0)
{
lean_object* v___x_4248_; 
lean_dec_ref(v_val_4246_);
lean_dec(v_indName_4101_);
v___x_4248_ = lean_box(0);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v___x_4248_;
goto v___jp_4206_;
}
else
{
lean_object* v_toConstantVal_4249_; lean_object* v_numParams_4250_; lean_object* v_all_4251_; lean_object* v_numNested_4252_; lean_object* v_type_4253_; lean_object* v___x_4254_; 
v_toConstantVal_4249_ = lean_ctor_get(v_val_4246_, 0);
lean_inc_ref(v_toConstantVal_4249_);
v_numParams_4250_ = lean_ctor_get(v_val_4246_, 1);
lean_inc(v_numParams_4250_);
v_all_4251_ = lean_ctor_get(v_val_4246_, 3);
lean_inc(v_all_4251_);
v_numNested_4252_ = lean_ctor_get(v_val_4246_, 5);
lean_inc(v_numNested_4252_);
lean_dec_ref(v_val_4246_);
v_type_4253_ = lean_ctor_get(v_toConstantVal_4249_, 2);
lean_inc_ref(v_type_4253_);
lean_dec_ref(v_toConstantVal_4249_);
v___x_4254_ = l_Lean_Meta_isPropFormerType(v_type_4253_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; uint8_t v___x_4256_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
v___x_4256_ = lean_unbox(v_a_4255_);
lean_dec(v_a_4255_);
if (v___x_4256_ == 0)
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
lean_inc_n(v_indName_4101_, 2);
v___x_4257_ = l_Lean_mkRecName(v_indName_4101_);
v___x_4258_ = l_Lean_mkBRecOnName(v_indName_4101_);
lean_inc(v_all_4251_);
v___x_4259_ = lean_array_mk(v_all_4251_);
lean_inc(v___x_4258_);
lean_inc_ref(v___x_4259_);
lean_inc(v_numParams_4250_);
lean_inc(v___x_4257_);
v___x_4260_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4257_, v_numParams_4250_, v___x_4259_, v___x_4258_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v___x_4261_; lean_object* v___x_4262_; uint8_t v___x_4263_; 
lean_dec_ref_known(v___x_4260_, 1);
v___x_4261_ = lean_unsigned_to_nat(0u);
v___x_4262_ = l_List_get_x21Internal___redArg(v___x_4111_, v_all_4251_, v___x_4261_);
lean_dec(v_all_4251_);
v___x_4263_ = lean_name_eq(v___x_4262_, v_indName_4101_);
lean_dec(v_indName_4101_);
lean_dec(v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
lean_dec_ref(v___x_4259_);
lean_dec(v___x_4258_);
lean_dec(v___x_4257_);
lean_dec(v_numNested_4252_);
lean_dec(v_numParams_4250_);
v___x_4264_ = lean_box(0);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v___x_4264_;
goto v___jp_4206_;
}
else
{
lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4265_ = lean_box(0);
v___x_4266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4252_, v___x_4257_, v___x_4258_, v_numParams_4250_, v___x_4259_, v___x_4261_, v___x_4265_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_numNested_4252_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_dec_ref_known(v___x_4266_, 1);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v___x_4265_;
goto v___jp_4206_;
}
else
{
lean_object* v_a_4267_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___x_4243_;
v_a_4214_ = v_a_4267_;
goto v___jp_4211_;
}
}
}
else
{
lean_dec_ref(v___x_4259_);
lean_dec(v___x_4258_);
lean_dec(v___x_4257_);
lean_dec(v_numNested_4252_);
lean_dec(v_all_4251_);
lean_dec(v_numParams_4250_);
lean_dec(v_indName_4101_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4268_; 
v_a_4268_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v___x_4260_, 1);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v_a_4268_;
goto v___jp_4206_;
}
else
{
lean_object* v_a_4269_; 
v_a_4269_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4260_, 1);
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___x_4243_;
v_a_4214_ = v_a_4269_;
goto v___jp_4211_;
}
}
}
else
{
lean_object* v___x_4270_; 
lean_dec(v_numNested_4252_);
lean_dec(v_all_4251_);
lean_dec(v_numParams_4250_);
lean_dec(v_indName_4101_);
v___x_4270_ = lean_box(0);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v___x_4270_;
goto v___jp_4206_;
}
}
else
{
lean_object* v_a_4271_; 
lean_dec(v_numNested_4252_);
lean_dec(v_all_4251_);
lean_dec(v_numParams_4250_);
lean_dec(v_indName_4101_);
v_a_4271_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4271_);
lean_dec_ref_known(v___x_4254_, 1);
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___x_4243_;
v_a_4214_ = v_a_4271_;
goto v___jp_4211_;
}
}
}
else
{
lean_object* v___x_4272_; 
lean_dec(v_a_4245_);
lean_dec(v_indName_4101_);
v___x_4272_ = lean_box(0);
v___y_4207_ = v_a_4240_;
v___y_4208_ = v___x_4243_;
v_a_4209_ = v___x_4272_;
goto v___jp_4206_;
}
}
else
{
lean_object* v_a_4273_; 
lean_dec(v_indName_4101_);
v_a_4273_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4273_);
lean_dec_ref_known(v___x_4244_, 1);
v___y_4212_ = v_a_4240_;
v___y_4213_ = v___x_4243_;
v_a_4214_ = v_a_4273_;
goto v___jp_4211_;
}
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_4101_);
v___x_4275_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4276_);
lean_dec_ref_known(v___x_4275_, 1);
if (lean_obj_tag(v_a_4276_) == 5)
{
lean_object* v_val_4277_; uint8_t v_isRec_4278_; 
v_val_4277_ = lean_ctor_get(v_a_4276_, 0);
lean_inc_ref(v_val_4277_);
lean_dec_ref_known(v_a_4276_, 1);
v_isRec_4278_ = lean_ctor_get_uint8(v_val_4277_, sizeof(void*)*6);
if (v_isRec_4278_ == 0)
{
lean_object* v___x_4279_; 
lean_dec_ref(v_val_4277_);
lean_dec(v_indName_4101_);
v___x_4279_ = lean_box(0);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v___x_4279_;
goto v___jp_4228_;
}
else
{
lean_object* v_toConstantVal_4280_; lean_object* v_numParams_4281_; lean_object* v_all_4282_; lean_object* v_numNested_4283_; lean_object* v_type_4284_; lean_object* v___x_4285_; 
v_toConstantVal_4280_ = lean_ctor_get(v_val_4277_, 0);
lean_inc_ref(v_toConstantVal_4280_);
v_numParams_4281_ = lean_ctor_get(v_val_4277_, 1);
lean_inc(v_numParams_4281_);
v_all_4282_ = lean_ctor_get(v_val_4277_, 3);
lean_inc(v_all_4282_);
v_numNested_4283_ = lean_ctor_get(v_val_4277_, 5);
lean_inc(v_numNested_4283_);
lean_dec_ref(v_val_4277_);
v_type_4284_ = lean_ctor_get(v_toConstantVal_4280_, 2);
lean_inc_ref(v_type_4284_);
lean_dec_ref(v_toConstantVal_4280_);
v___x_4285_ = l_Lean_Meta_isPropFormerType(v_type_4284_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; uint8_t v___x_4287_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4286_);
lean_dec_ref_known(v___x_4285_, 1);
v___x_4287_ = lean_unbox(v_a_4286_);
lean_dec(v_a_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_inc_n(v_indName_4101_, 2);
v___x_4288_ = l_Lean_mkRecName(v_indName_4101_);
v___x_4289_ = l_Lean_mkBRecOnName(v_indName_4101_);
lean_inc(v_all_4282_);
v___x_4290_ = lean_array_mk(v_all_4282_);
lean_inc(v___x_4289_);
lean_inc_ref(v___x_4290_);
lean_inc(v_numParams_4281_);
lean_inc(v___x_4288_);
v___x_4291_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4288_, v_numParams_4281_, v___x_4290_, v___x_4289_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v___x_4292_; lean_object* v___x_4293_; uint8_t v___x_4294_; 
lean_dec_ref_known(v___x_4291_, 1);
v___x_4292_ = lean_unsigned_to_nat(0u);
v___x_4293_ = l_List_get_x21Internal___redArg(v___x_4111_, v_all_4282_, v___x_4292_);
lean_dec(v_all_4282_);
v___x_4294_ = lean_name_eq(v___x_4293_, v_indName_4101_);
lean_dec(v_indName_4101_);
lean_dec(v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; 
lean_dec_ref(v___x_4290_);
lean_dec(v___x_4289_);
lean_dec(v___x_4288_);
lean_dec(v_numNested_4283_);
lean_dec(v_numParams_4281_);
v___x_4295_ = lean_box(0);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v___x_4295_;
goto v___jp_4228_;
}
else
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_box(0);
v___x_4297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4283_, v___x_4288_, v___x_4289_, v_numParams_4281_, v___x_4290_, v___x_4292_, v___x_4296_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_numNested_4283_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_dec_ref_known(v___x_4297_, 1);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v___x_4296_;
goto v___jp_4228_;
}
else
{
lean_object* v_a_4298_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___y_4234_ = v_a_4240_;
v___y_4235_ = v___x_4274_;
v_a_4236_ = v_a_4298_;
goto v___jp_4233_;
}
}
}
else
{
lean_dec_ref(v___x_4290_);
lean_dec(v___x_4289_);
lean_dec(v___x_4288_);
lean_dec(v_numNested_4283_);
lean_dec(v_all_4282_);
lean_dec(v_numParams_4281_);
lean_dec(v_indName_4101_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4299_; 
v_a_4299_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4291_, 1);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v_a_4299_;
goto v___jp_4228_;
}
else
{
lean_object* v_a_4300_; 
v_a_4300_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4291_, 1);
v___y_4234_ = v_a_4240_;
v___y_4235_ = v___x_4274_;
v_a_4236_ = v_a_4300_;
goto v___jp_4233_;
}
}
}
else
{
lean_object* v___x_4301_; 
lean_dec(v_numNested_4283_);
lean_dec(v_all_4282_);
lean_dec(v_numParams_4281_);
lean_dec(v_indName_4101_);
v___x_4301_ = lean_box(0);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v___x_4301_;
goto v___jp_4228_;
}
}
else
{
lean_object* v_a_4302_; 
lean_dec(v_numNested_4283_);
lean_dec(v_all_4282_);
lean_dec(v_numParams_4281_);
lean_dec(v_indName_4101_);
v_a_4302_ = lean_ctor_get(v___x_4285_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4285_, 1);
v___y_4234_ = v_a_4240_;
v___y_4235_ = v___x_4274_;
v_a_4236_ = v_a_4302_;
goto v___jp_4233_;
}
}
}
else
{
lean_object* v___x_4303_; 
lean_dec(v_a_4276_);
lean_dec(v_indName_4101_);
v___x_4303_ = lean_box(0);
v___y_4229_ = v_a_4240_;
v___y_4230_ = v___x_4274_;
v_a_4231_ = v___x_4303_;
goto v___jp_4228_;
}
}
else
{
lean_object* v_a_4304_; 
lean_dec(v_indName_4101_);
v_a_4304_ = lean_ctor_get(v___x_4275_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4275_, 1);
v___y_4234_ = v_a_4240_;
v___y_4235_ = v___x_4274_;
v_a_4236_ = v_a_4304_;
goto v___jp_4233_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkBRecOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_4101_ = stack[0].m_obj;
lean_object* v_a_4102_ = stack[1].m_obj;
lean_object* v_a_4103_ = stack[2].m_obj;
lean_object* v_a_4104_ = stack[3].m_obj;
lean_object* v_a_4105_ = stack[4].m_obj;
lean_object* v_res_4381_;
v_res_4381_ = l_Lean_mkBRecOn(v_indName_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
stack->m_obj
 = v_res_4381_;
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_){
_start:
{
lean_object* v_res_4388_; 
v_res_4388_ = l_Lean_mkBRecOn(v_indName_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
return v_res_4388_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4389_, lean_object* v___x_4390_, lean_object* v___x_4391_, lean_object* v___x_4392_, lean_object* v___x_4393_, lean_object* v_inst_4394_, lean_object* v_R_4395_, lean_object* v_a_4396_, lean_object* v_b_4397_, lean_object* v_c_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; 
v___x_4404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4389_, v___x_4390_, v___x_4391_, v___x_4392_, v___x_4393_, v_a_4396_, v_b_4397_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
return v___x_4404_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_4389_ = stack[0].m_obj;
lean_object* v___x_4390_ = stack[1].m_obj;
lean_object* v___x_4391_ = stack[2].m_obj;
lean_object* v___x_4392_ = stack[3].m_obj;
lean_object* v___x_4393_ = stack[4].m_obj;
lean_object* v_a_4396_ = stack[7].m_obj;
lean_object* v_b_4397_ = stack[8].m_obj;
lean_object* v___y_4399_ = stack[10].m_obj;
lean_object* v___y_4400_ = stack[11].m_obj;
lean_object* v___y_4401_ = stack[12].m_obj;
lean_object* v___y_4402_ = stack[13].m_obj;
lean_object* v_res_4405_;
v_res_4405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4389_, v___x_4390_, v___x_4391_, v___x_4392_, v___x_4393_, lean_box(0), lean_box(0), v_a_4396_, v_b_4397_, lean_box(0), v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
stack->m_obj
 = v_res_4405_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4406_, lean_object* v___x_4407_, lean_object* v___x_4408_, lean_object* v___x_4409_, lean_object* v___x_4410_, lean_object* v_inst_4411_, lean_object* v_R_4412_, lean_object* v_a_4413_, lean_object* v_b_4414_, lean_object* v_c_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_){
_start:
{
lean_object* v_res_4421_; 
v_res_4421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4406_, v___x_4407_, v___x_4408_, v___x_4409_, v___x_4410_, v_inst_4411_, v_R_4412_, v_a_4413_, v_b_4414_, v_c_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v_upperBound_4406_);
return v_res_4421_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4467_ = lean_unsigned_to_nat(2304625798u);
v___x_4468_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4469_ = l_Lean_Name_num___override(v___x_4468_, v___x_4467_);
return v___x_4469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4471_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4472_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4473_ = l_Lean_Name_str___override(v___x_4472_, v___x_4471_);
return v___x_4473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4476_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4477_ = l_Lean_Name_str___override(v___x_4476_, v___x_4475_);
return v___x_4477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4478_ = lean_unsigned_to_nat(2u);
v___x_4479_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4480_ = l_Lean_Name_num___override(v___x_4479_, v___x_4478_);
return v___x_4480_;
}
}
lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4482_; uint8_t v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v___x_4482_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4483_ = 0;
v___x_4484_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4485_ = l_Lean_registerTraceClass(v___x_4482_, v___x_4483_, v___x_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4486_;
v_res_4486_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4486_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4488_;
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
