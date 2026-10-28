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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v___x_203_; size_t v___x_204_; uint8_t v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_201_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__0_spec__0(v_a_199_, v_as_198_, v___x_203_, v___x_204_);
return v___x_205_;
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
lean_object* v___f_435_; lean_object* v___x_5029__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_5029__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_5029__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
lean_object* v___x_452_; uint8_t v___y_454_; lean_object* v_env_462_; uint8_t v___x_463_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_env_462_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref_n(v_env_462_, 2);
lean_dec(v___x_452_);
v___x_463_ = l_Lean_Environment_hasUnsafe(v_env_462_, v_type_447_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
v___x_464_ = l_Lean_Environment_hasUnsafe(v_env_462_, v_value_448_);
if (v___x_464_ == 0)
{
uint8_t v___x_465_; 
v___x_465_ = 1;
v___y_454_ = v___x_465_;
goto v___jp_453_;
}
else
{
goto v___jp_460_;
}
}
else
{
lean_dec_ref(v_env_462_);
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
uint8_t v___x_461_; 
v___x_461_ = 0;
v___y_454_ = v___x_461_;
goto v___jp_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg___boxed(lean_object* v_name_466_, lean_object* v_levelParams_467_, lean_object* v_type_468_, lean_object* v_value_469_, lean_object* v_hints_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_466_, v_levelParams_467_, v_type_468_, v_value_469_, v_hints_470_, v___y_471_);
lean_dec(v___y_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(lean_object* v_name_474_, lean_object* v_levelParams_475_, lean_object* v_type_476_, lean_object* v_value_477_, lean_object* v_hints_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_name_474_, v_levelParams_475_, v_type_476_, v_value_477_, v_hints_478_, v___y_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___boxed(lean_object* v_name_485_, lean_object* v_levelParams_486_, lean_object* v_type_487_, lean_object* v_value_488_, lean_object* v_hints_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5(v_name_485_, v_levelParams_486_, v_type_487_, v_value_488_, v_hints_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v_as_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v___x_497_);
lean_dec(v___x_496_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_501_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_array_uget_borrowed(v_as_498_, v_i_500_);
lean_inc(v___y_505_);
lean_inc_ref(v___y_504_);
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v_a_509_);
v___x_510_ = lean_infer_type(v_a_509_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
lean_inc_ref(v___x_497_);
lean_inc(v___x_496_);
v___x_512_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v___x_496_, v___x_497_, v_a_511_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; size_t v___x_515_; size_t v___x_516_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_512_, 1);
v___x_514_ = l_Lean_Expr_app___override(v_b_501_, v_a_513_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_add(v_i_500_, v___x_515_);
v_i_500_ = v___x_516_;
v_b_501_ = v___x_514_;
goto _start;
}
else
{
lean_dec_ref(v_b_501_);
lean_dec_ref(v___x_497_);
lean_dec(v___x_496_);
return v___x_512_;
}
}
else
{
lean_dec_ref(v_b_501_);
lean_dec_ref(v___x_497_);
lean_dec(v___x_496_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4___boxed(lean_object* v___x_518_, lean_object* v___x_519_, lean_object* v_as_520_, lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
size_t v_sz_boxed_529_; size_t v_i_boxed_530_; lean_object* v_res_531_; 
v_sz_boxed_529_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_530_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_518_, v___x_519_, v_as_520_, v_sz_boxed_529_, v_i_boxed_530_, v_b_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v_as_520_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(lean_object* v___x_532_, uint8_t v___x_533_, lean_object* v_targs_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v___x_541_ = l_Lean_Expr_sort___override(v___x_532_);
v___x_542_ = 0;
v___x_543_ = 1;
v___x_544_ = l_Lean_Meta_mkLambdaFVars(v_targs_534_, v___x_541_, v___x_542_, v___x_533_, v___x_542_, v___x_533_, v___x_543_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed(lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_targs_547_, lean_object* v_x_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_9246__boxed_554_; lean_object* v_res_555_; 
v___x_9246__boxed_554_ = lean_unbox(v___x_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_545_, v___x_9246__boxed_554_, v_targs_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec_ref(v_x_548_);
lean_dec_ref(v_targs_547_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v_as_559_, size_t v_sz_560_, size_t v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_lt(v_i_561_, v_sz_560_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_dec(v___x_556_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v_b_562_);
return v___x_569_;
}
else
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___f_572_; lean_object* v_a_573_; lean_object* v___x_574_; 
v___x_570_ = lean_nat_dec_lt(v___x_557_, v___x_558_);
v___x_571_ = lean_box(v___x_570_);
lean_inc(v___x_556_);
v___f_572_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_572_, 0, v___x_556_);
lean_closure_set(v___f_572_, 1, v___x_571_);
v_a_573_ = lean_array_uget_borrowed(v_as_559_, v_i_561_);
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v_a_573_);
v___x_574_ = lean_infer_type(v_a_573_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; uint8_t v___x_576_; lean_object* v___x_577_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = 0;
v___x_577_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_575_, v___f_572_, v___x_576_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; size_t v___x_580_; size_t v___x_581_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = l_Lean_Expr_app___override(v_b_562_, v_a_578_);
v___x_580_ = ((size_t)1ULL);
v___x_581_ = lean_usize_add(v_i_561_, v___x_580_);
v_i_561_ = v___x_581_;
v_b_562_ = v___x_579_;
goto _start;
}
else
{
lean_dec_ref(v_b_562_);
lean_dec(v___x_556_);
return v___x_577_;
}
}
else
{
lean_dec_ref(v___f_572_);
lean_dec_ref(v_b_562_);
lean_dec(v___x_556_);
return v___x_574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object* v___x_583_, lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v_as_586_, lean_object* v_sz_587_, lean_object* v_i_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
size_t v_sz_boxed_595_; size_t v_i_boxed_596_; lean_object* v_res_597_; 
v_sz_boxed_595_ = lean_unbox_usize(v_sz_587_);
lean_dec(v_sz_587_);
v_i_boxed_596_ = lean_unbox_usize(v_i_588_);
lean_dec(v_i_588_);
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_583_, v___x_584_, v___x_585_, v_as_586_, v_sz_boxed_595_, v_i_boxed_596_, v_b_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_as_586_);
lean_dec(v___x_585_);
lean_dec(v___x_584_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(lean_object* v_msgData_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v___x_604_; lean_object* v_env_605_; uint8_t v___x_606_; lean_object* v_env_607_; lean_object* v___x_608_; lean_object* v_toCold_609_; lean_object* v_mctx_610_; lean_object* v_lctx_611_; lean_object* v_options_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_604_ = lean_st_ref_get(v___y_602_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v___x_606_ = 0;
v_env_607_ = l_Lean_Environment_setRecordingDeps(v_env_605_, v___x_606_);
v___x_608_ = lean_st_ref_get(v___y_600_);
v_toCold_609_ = lean_ctor_get(v___y_601_, 0);
v_mctx_610_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref(v_mctx_610_);
lean_dec(v___x_608_);
v_lctx_611_ = lean_ctor_get(v___y_599_, 2);
v_options_612_ = lean_ctor_get(v_toCold_609_, 2);
lean_inc_ref(v_options_612_);
lean_inc_ref(v_lctx_611_);
v___x_613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_613_, 0, v_env_607_);
lean_ctor_set(v___x_613_, 1, v_mctx_610_);
lean_ctor_set(v___x_613_, 2, v_lctx_611_);
lean_ctor_set(v___x_613_, 3, v_options_612_);
v___x_614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v_msgData_598_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_ref_629_; lean_object* v___x_630_; lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
v_ref_629_ = lean_ctor_get(v___y_626_, 2);
v___x_630_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_inc(v_ref_629_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_ref_629_);
lean_ctor_set(v___x_635_, 1, v_a_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set_tag(v___x_633_, 1);
lean_ctor_set(v___x_633_, 0, v___x_635_);
v___x_637_ = v___x_633_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
return v_res_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_651_ = lean_unsigned_to_nat(4u);
v___x_652_ = lean_unsigned_to_nat(68u);
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_655_ = l_mkPanicMessageWithDecl(v___x_654_, v___x_653_, v___x_652_, v___x_651_, v___x_650_);
return v___x_655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_662_, lean_object* v_numMotives_663_, lean_object* v_numMinors_664_, lean_object* v___x_665_, lean_object* v_head_666_, lean_object* v_tail_667_, lean_object* v_recName_668_, lean_object* v_belowName_669_, lean_object* v_levelParams_670_, lean_object* v_refArgs_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_678_ = lean_nat_add(v_nParams_662_, v_numMotives_663_);
v___x_679_ = lean_nat_add(v___x_678_, v_numMinors_664_);
v___x_680_ = lean_array_get_size(v_refArgs_671_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___x_679_);
lean_dec(v___x_678_);
lean_dec_ref(v_refArgs_671_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
lean_dec(v_recName_668_);
lean_dec(v_tail_667_);
lean_dec(v_head_666_);
lean_dec(v_nParams_662_);
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_683_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_682_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_684_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_662_);
lean_inc_ref_n(v_refArgs_671_, 4);
v___x_685_ = l_Array_toSubarray___redArg(v_refArgs_671_, v___x_684_, v_nParams_662_);
v___x_686_ = l_Subarray_copy___redArg(v___x_685_);
lean_inc(v___x_678_);
v___x_687_ = l_Array_toSubarray___redArg(v_refArgs_671_, v_nParams_662_, v___x_678_);
v___x_688_ = l_Subarray_copy___redArg(v___x_687_);
lean_inc_n(v___x_679_, 2);
v___x_689_ = l_Array_toSubarray___redArg(v_refArgs_671_, v___x_678_, v___x_679_);
v___x_690_ = l_Subarray_copy___redArg(v___x_689_);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_sub(v___x_680_, v___x_691_);
lean_inc(v___x_692_);
v___x_693_ = l_Array_toSubarray___redArg(v_refArgs_671_, v___x_679_, v___x_692_);
v___x_694_ = l_Subarray_copy___redArg(v___x_693_);
v___x_695_ = lean_array_get(v___x_665_, v_refArgs_671_, v___x_692_);
lean_dec(v___x_692_);
lean_dec_ref(v_refArgs_671_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___x_695_);
v___x_696_ = lean_infer_type(v___x_695_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
v___x_698_ = lean_infer_type(v_a_697_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = l_Lean_Meta_typeFormerTypeLevel(v_a_699_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
if (lean_obj_tag(v_a_701_) == 1)
{
lean_object* v_val_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; size_t v_sz_708_; size_t v___x_709_; lean_object* v___x_710_; 
v_val_702_ = lean_ctor_get(v_a_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_a_701_, 1);
v___x_703_ = l_Lean_mkLevelMax(v_val_702_, v_head_666_);
lean_inc_n(v___x_703_, 2);
v___x_704_ = l_Lean_Level_succ___override(v___x_703_);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
lean_ctor_set(v___x_705_, 1, v_tail_667_);
v___x_706_ = l_Lean_Expr_const___override(v_recName_668_, v___x_705_);
v___x_707_ = l_Lean_mkAppN(v___x_706_, v___x_686_);
v_sz_708_ = lean_array_size(v___x_688_);
v___x_709_ = ((size_t)0ULL);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_703_, v___x_679_, v___x_680_, v___x_688_, v_sz_708_, v___x_709_, v___x_707_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___x_679_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; size_t v_sz_712_; lean_object* v___x_713_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_sz_712_ = lean_array_size(v___x_690_);
lean_inc_ref(v___x_688_);
lean_inc(v___x_703_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_703_, v___x_688_, v___x_690_, v_sz_712_, v___x_709_, v_a_711_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = l_Lean_mkAppN(v_a_714_, v___x_694_);
lean_inc(v___x_695_);
v___x_716_ = l_Lean_Expr_app___override(v___x_715_, v___x_695_);
v___x_717_ = l_Array_append___redArg(v___x_686_, v___x_688_);
lean_dec_ref(v___x_688_);
v___x_718_ = l_Array_append___redArg(v___x_717_, v___x_694_);
lean_dec_ref(v___x_694_);
v___x_719_ = lean_mk_empty_array_with_capacity(v___x_691_);
v___x_720_ = lean_array_push(v___x_719_, v___x_695_);
v___x_721_ = l_Array_append___redArg(v___x_718_, v___x_720_);
lean_dec_ref(v___x_720_);
v___x_722_ = l_Lean_Expr_sort___override(v___x_703_);
v___x_723_ = 0;
v___x_724_ = 1;
v___x_725_ = l_Lean_Meta_mkForallFVars(v___x_721_, v___x_722_, v___x_723_, v___x_681_, v___x_681_, v___x_724_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Meta_mkLambdaFVars(v___x_721_, v___x_716_, v___x_723_, v___x_681_, v___x_723_, v___x_681_, v___x_724_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___x_721_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = lean_box(1);
v___x_730_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_669_, v_levelParams_670_, v_a_726_, v_a_728_, v___x_729_, v___y_676_);
return v___x_730_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_a_726_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
v_a_731_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_727_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec_ref(v___x_721_);
lean_dec_ref(v___x_716_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
v_a_739_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_725_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_725_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_703_);
lean_dec(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
v_a_747_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_713_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_713_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v___x_703_);
lean_dec(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
v_a_755_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_710_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_710_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_a_701_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_679_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
lean_dec(v_recName_668_);
lean_dec(v_tail_667_);
lean_dec(v_head_666_);
v___x_763_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_764_ = l_Lean_MessageData_ofExpr(v___x_695_);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_767_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
return v___x_768_;
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_679_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
lean_dec(v_recName_668_);
lean_dec(v_tail_667_);
lean_dec(v_head_666_);
v_a_769_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_700_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_700_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_679_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
lean_dec(v_recName_668_);
lean_dec(v_tail_667_);
lean_dec(v_head_666_);
v_a_777_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_698_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_698_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v___x_695_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_679_);
lean_dec(v_levelParams_670_);
lean_dec(v_belowName_669_);
lean_dec(v_recName_668_);
lean_dec(v_tail_667_);
lean_dec(v_head_666_);
v_a_785_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_696_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_696_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_793_, lean_object* v_numMotives_794_, lean_object* v_numMinors_795_, lean_object* v___x_796_, lean_object* v_head_797_, lean_object* v_tail_798_, lean_object* v_recName_799_, lean_object* v_belowName_800_, lean_object* v_levelParams_801_, lean_object* v_refArgs_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_793_, v_numMotives_794_, v_numMinors_795_, v___x_796_, v_head_797_, v_tail_798_, v_recName_799_, v_belowName_800_, v_levelParams_801_, v_refArgs_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_x_803_);
lean_dec_ref(v___x_796_);
lean_dec(v_numMinors_795_);
lean_dec(v_numMotives_794_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_810_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg(){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__1);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___boxed(lean_object* v___dummy_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg();
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
if (lean_obj_tag(v_a_817_) == 0)
{
lean_object* v___x_819_; 
v___x_819_ = l_List_reverse___redArg(v_a_818_);
return v___x_819_;
}
else
{
lean_object* v_head_820_; lean_object* v_tail_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_830_; 
v_head_820_ = lean_ctor_get(v_a_817_, 0);
v_tail_821_ = lean_ctor_get(v_a_817_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_830_ == 0)
{
v___x_823_ = v_a_817_;
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_tail_821_);
lean_inc(v_head_820_);
lean_dec(v_a_817_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_830_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = l_Lean_Level_param___override(v_head_820_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v_a_818_);
lean_ctor_set(v___x_823_, 0, v___x_825_);
v___x_827_ = v___x_823_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_a_818_);
v___x_827_ = v_reuseFailAlloc_829_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
v_a_817_ = v_tail_821_;
v_a_818_ = v___x_827_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg();
return v___x_835_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_837_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
v___x_838_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___x_836_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v___x_836_);
lean_ctor_set(v___x_838_, 4, v___x_836_);
lean_ctor_set(v___x_838_, 5, v___x_836_);
lean_ctor_set(v___x_838_, 6, v___x_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_839_, uint8_t v_s_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_env_845_; lean_object* v_nextMacroScope_846_; lean_object* v_ngen_847_; lean_object* v_auxDeclNGen_848_; lean_object* v_traceState_849_; lean_object* v_recordedDeps_850_; lean_object* v_messages_851_; lean_object* v_infoState_852_; lean_object* v_snapshotTasks_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_882_; 
v___x_844_ = lean_st_ref_take(v___y_842_);
v_env_845_ = lean_ctor_get(v___x_844_, 0);
v_nextMacroScope_846_ = lean_ctor_get(v___x_844_, 1);
v_ngen_847_ = lean_ctor_get(v___x_844_, 2);
v_auxDeclNGen_848_ = lean_ctor_get(v___x_844_, 3);
v_traceState_849_ = lean_ctor_get(v___x_844_, 4);
v_recordedDeps_850_ = lean_ctor_get(v___x_844_, 6);
v_messages_851_ = lean_ctor_get(v___x_844_, 7);
v_infoState_852_ = lean_ctor_get(v___x_844_, 8);
v_snapshotTasks_853_ = lean_ctor_get(v___x_844_, 9);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_844_, 5);
lean_dec(v_unused_883_);
v___x_855_ = v___x_844_;
v_isShared_856_ = v_isSharedCheck_882_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snapshotTasks_853_);
lean_inc(v_infoState_852_);
lean_inc(v_messages_851_);
lean_inc(v_recordedDeps_850_);
lean_inc(v_traceState_849_);
lean_inc(v_auxDeclNGen_848_);
lean_inc(v_ngen_847_);
lean_inc(v_nextMacroScope_846_);
lean_inc(v_env_845_);
lean_dec(v___x_844_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_882_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint8_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_857_ = 0;
v___x_858_ = lean_box(0);
v___x_859_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_845_, v_declName_839_, v_s_840_, v___x_857_, v___x_858_);
v___x_860_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 5, v___x_860_);
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_nextMacroScope_846_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_ngen_847_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_auxDeclNGen_848_);
lean_ctor_set(v_reuseFailAlloc_881_, 4, v_traceState_849_);
lean_ctor_set(v_reuseFailAlloc_881_, 5, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_881_, 6, v_recordedDeps_850_);
lean_ctor_set(v_reuseFailAlloc_881_, 7, v_messages_851_);
lean_ctor_set(v_reuseFailAlloc_881_, 8, v_infoState_852_);
lean_ctor_set(v_reuseFailAlloc_881_, 9, v_snapshotTasks_853_);
v___x_862_ = v_reuseFailAlloc_881_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_mctx_865_; lean_object* v_zetaDeltaFVarIds_866_; lean_object* v_postponed_867_; lean_object* v_diag_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_879_; 
v___x_863_ = lean_st_ref_put(v___y_842_, v___x_862_);
v___x_864_ = lean_st_ref_take(v___y_841_);
v_mctx_865_ = lean_ctor_get(v___x_864_, 0);
v_zetaDeltaFVarIds_866_ = lean_ctor_get(v___x_864_, 2);
v_postponed_867_ = lean_ctor_get(v___x_864_, 3);
v_diag_868_ = lean_ctor_get(v___x_864_, 4);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v___x_864_, 1);
lean_dec(v_unused_880_);
v___x_870_ = v___x_864_;
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_diag_868_);
lean_inc(v_postponed_867_);
lean_inc(v_zetaDeltaFVarIds_866_);
lean_inc(v_mctx_865_);
lean_dec(v___x_864_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_879_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = lean_box(0);
v___x_873_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 1, v___x_873_);
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_mctx_865_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_zetaDeltaFVarIds_866_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_postponed_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_diag_868_);
v___x_875_ = v_reuseFailAlloc_878_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_st_ref_put(v___y_841_, v___x_875_);
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v___x_872_);
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_884_, lean_object* v_s_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_s_boxed_889_; lean_object* v_res_890_; 
v_s_boxed_889_ = lean_unbox(v_s_885_);
v_res_890_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_884_, v_s_boxed_889_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec(v___y_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; lean_object* v___x_898_; 
v___x_897_ = 0;
v___x_898_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_891_, v___x_897_, v___y_893_, v___y_895_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(lean_object* v_ref_906_, lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_toCold_913_; lean_object* v_currRecDepth_914_; lean_object* v_ref_915_; uint16_t v_optionFlags_916_; uint8_t v_suppressElabErrors_917_; uint8_t v_checkDeprecated_918_; uint8_t v_isRecordingDeps_919_; lean_object* v_ref_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_toCold_913_ = lean_ctor_get(v___y_910_, 0);
v_currRecDepth_914_ = lean_ctor_get(v___y_910_, 1);
v_ref_915_ = lean_ctor_get(v___y_910_, 2);
v_optionFlags_916_ = lean_ctor_get_uint16(v___y_910_, sizeof(void*)*3);
v_suppressElabErrors_917_ = lean_ctor_get_uint8(v___y_910_, sizeof(void*)*3 + 2);
v_checkDeprecated_918_ = lean_ctor_get_uint8(v___y_910_, sizeof(void*)*3 + 3);
v_isRecordingDeps_919_ = lean_ctor_get_uint8(v___y_910_, sizeof(void*)*3 + 4);
v_ref_920_ = l_Lean_replaceRef(v_ref_906_, v_ref_915_);
lean_inc(v_currRecDepth_914_);
lean_inc_ref(v_toCold_913_);
v___x_921_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_921_, 0, v_toCold_913_);
lean_ctor_set(v___x_921_, 1, v_currRecDepth_914_);
lean_ctor_set(v___x_921_, 2, v_ref_920_);
lean_ctor_set_uint16(v___x_921_, sizeof(void*)*3, v_optionFlags_916_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*3 + 2, v_suppressElabErrors_917_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*3 + 3, v_checkDeprecated_918_);
lean_ctor_set_uint8(v___x_921_, sizeof(void*)*3 + 4, v_isRecordingDeps_919_);
v___x_922_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_907_, v___y_908_, v___y_909_, v___x_921_, v___y_911_);
lean_dec_ref_known(v___x_921_, 3);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg___boxed(lean_object* v_ref_923_, lean_object* v_msg_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_923_, v_msg_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v_ref_923_);
return v_res_930_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_933_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
lean_ctor_set(v___x_936_, 2, v___x_935_);
lean_ctor_set(v___x_936_, 3, v___x_935_);
lean_ctor_set(v___x_936_, 4, v___x_934_);
lean_ctor_set(v___x_936_, 5, v___x_934_);
lean_ctor_set(v___x_936_, 6, v___x_934_);
lean_ctor_set(v___x_936_, 7, v___x_934_);
lean_ctor_set(v___x_936_, 8, v___x_934_);
lean_ctor_set(v___x_936_, 9, v___x_934_);
lean_ctor_set(v___x_936_, 10, v___x_934_);
lean_ctor_set(v___x_936_, 11, v___x_933_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(32u);
v___x_938_ = lean_mk_empty_array_with_capacity(v___x_937_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3(void){
_start:
{
size_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_940_ = ((size_t)5ULL);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_unsigned_to_nat(32u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___x_944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
lean_ctor_set(v___x_945_, 2, v___x_941_);
lean_ctor_set(v___x_945_, 3, v___x_941_);
lean_ctor_set_usize(v___x_945_, 4, v___x_940_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = lean_box(1);
v___x_947_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3);
v___x_948_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v___x_946_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__5));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__7));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__9));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__11));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__13));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(lean_object* v_msg_971_, lean_object* v_declHint_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v_env_977_; uint8_t v___x_978_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_st_ref_get(v___y_973_);
v_env_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_ref(v_env_977_);
lean_dec(v___x_976_);
v___x_978_ = l_Lean_Name_isAnonymous(v_declHint_972_);
if (v___x_978_ == 0)
{
uint8_t v_isExporting_979_; 
v_isExporting_979_ = lean_ctor_get_uint8(v_env_977_, sizeof(void*)*13);
if (v_isExporting_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_env_977_);
lean_dec(v_declHint_972_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_msg_971_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
lean_inc_ref(v_env_977_);
v___x_981_ = l_Lean_Environment_setExporting(v_env_977_, v___x_978_);
lean_inc(v_declHint_972_);
lean_inc_ref(v___x_981_);
v___x_982_ = l_Lean_Environment_contains(v___x_981_, v_declHint_972_, v_isExporting_979_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; 
lean_dec_ref(v___x_981_);
lean_dec_ref(v_env_977_);
lean_dec(v_declHint_972_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v_msg_971_);
return v___x_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_c_989_; lean_object* v___x_990_; 
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4);
v___x_986_ = l_Lean_Options_empty;
lean_inc_ref(v___x_981_);
v___x_987_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_987_, 0, v___x_981_);
lean_ctor_set(v___x_987_, 1, v___x_984_);
lean_ctor_set(v___x_987_, 2, v___x_985_);
lean_ctor_set(v___x_987_, 3, v___x_986_);
lean_inc(v_declHint_972_);
v___x_988_ = l_Lean_MessageData_ofConstName(v_declHint_972_, v___x_978_);
v_c_989_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_989_, 0, v___x_987_);
lean_ctor_set(v_c_989_, 1, v___x_988_);
v___x_990_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_981_, v_declHint_972_);
lean_dec_ref(v___x_981_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
lean_dec_ref(v_env_977_);
lean_dec(v_declHint_972_);
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_c_989_);
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_MessageData_note(v___x_994_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v_msg_971_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
return v___x_997_;
}
else
{
lean_object* v_val_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1032_; 
v_val_998_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1000_ = v___x_990_;
v_isShared_1001_ = v_isSharedCheck_1032_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_val_998_);
lean_dec(v___x_990_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1032_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v_moduleNames_1003_; lean_object* v_mod_1004_; uint8_t v___x_1005_; 
v___x_1002_ = l_Lean_Environment_header(v_env_977_);
lean_dec_ref(v_env_977_);
v_moduleNames_1003_ = lean_ctor_get(v___x_1002_, 4);
lean_inc_ref(v_moduleNames_1003_);
lean_dec_ref(v___x_1002_);
v_mod_1004_ = lean_array_get(v___x_975_, v_moduleNames_1003_, v_val_998_);
lean_dec(v_val_998_);
lean_dec_ref(v_moduleNames_1003_);
v___x_1005_ = l_Lean_isPrivateName(v_declHint_972_);
lean_dec(v_declHint_972_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_c_989_);
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_MessageData_ofName(v_mod_1004_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_MessageData_note(v___x_1013_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_msg_971_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 0);
lean_ctor_set(v___x_1000_, 0, v___x_1015_);
v___x_1017_ = v___x_1000_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_c_989_);
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = l_Lean_MessageData_ofName(v_mod_1004_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_MessageData_note(v___x_1026_);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_msg_971_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set_tag(v___x_1000_, 0);
lean_ctor_set(v___x_1000_, 0, v___x_1028_);
v___x_1030_ = v___x_1000_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
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
}
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v_env_977_);
lean_dec(v_declHint_972_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_msg_971_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_msg_1034_, lean_object* v_declHint_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1034_, v_declHint_1035_, v___y_1036_);
lean_dec(v___y_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(lean_object* v_msg_1039_, lean_object* v_declHint_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1056_; 
v___x_1046_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1039_, v_declHint_1040_, v___y_1044_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1056_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1051_ = l_Lean_unknownIdentifierMessageTag;
v___x_1052_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_a_1047_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1052_);
v___x_1054_ = v___x_1049_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14___boxed(lean_object* v_msg_1057_, lean_object* v_declHint_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1057_, v_declHint_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_ref_1065_, lean_object* v_msg_1066_, lean_object* v_declHint_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1073_; lean_object* v_a_1074_; lean_object* v___x_1075_; 
v___x_1073_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1066_, v_declHint_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1065_, v_a_1074_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object* v_ref_1076_, lean_object* v_msg_1077_, lean_object* v_declHint_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1076_, v_msg_1077_, v_declHint_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_ref_1076_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1091_, lean_object* v_constName_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1098_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1099_ = 0;
lean_inc(v_constName_1092_);
v___x_1100_ = l_Lean_MessageData_ofConstName(v_constName_1092_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1098_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1091_, v___x_1103_, v_constName_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1105_, lean_object* v_constName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1105_, v_constName_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v_ref_1105_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_ref_1119_; lean_object* v___x_1120_; 
v_ref_1119_ = lean_ctor_get(v___y_1116_, 2);
v___x_1120_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1119_, v_constName_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_env_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_st_ref_get(v___y_1132_);
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_ref(v_env_1135_);
lean_dec(v___x_1134_);
v___x_1136_ = 0;
lean_inc(v_constName_1128_);
v___x_1137_ = l_Lean_Environment_find_x3f(v_env_1135_, v_constName_1128_, v___x_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1138_;
}
else
{
lean_object* v_val_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_constName_1128_);
v_val_1139_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1137_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_val_1139_);
lean_dec(v___x_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_val_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1163_, lean_object* v_nParams_1164_, lean_object* v_belowName_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1163_);
v___x_1172_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1163_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
if (lean_obj_tag(v_a_1173_) == 7)
{
lean_object* v_val_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1291_; 
v_val_1174_ = lean_ctor_get(v_a_1173_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1173_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1176_ = v_a_1173_;
v_isShared_1177_ = v_isSharedCheck_1291_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_val_1174_);
lean_dec(v_a_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1291_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v_toConstantVal_1178_; lean_object* v_numMotives_1179_; lean_object* v_numMinors_1180_; lean_object* v_levelParams_1181_; lean_object* v_type_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_toConstantVal_1178_ = lean_ctor_get(v_val_1174_, 0);
lean_inc_ref(v_toConstantVal_1178_);
v_numMotives_1179_ = lean_ctor_get(v_val_1174_, 4);
lean_inc(v_numMotives_1179_);
v_numMinors_1180_ = lean_ctor_get(v_val_1174_, 5);
lean_inc(v_numMinors_1180_);
lean_dec_ref(v_val_1174_);
v_levelParams_1181_ = lean_ctor_get(v_toConstantVal_1178_, 1);
lean_inc_n(v_levelParams_1181_, 2);
v_type_1182_ = lean_ctor_get(v_toConstantVal_1178_, 2);
lean_inc_ref(v_type_1182_);
lean_dec_ref(v_toConstantVal_1178_);
v___x_1183_ = lean_box(0);
v___x_1184_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1181_, v___x_1183_);
if (lean_obj_tag(v___x_1184_) == 1)
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v___f_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
v_head_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_head_1185_);
v_tail_1186_ = lean_ctor_get(v___x_1184_, 1);
lean_inc(v_tail_1186_);
lean_dec_ref_known(v___x_1184_, 2);
v___f_1187_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1187_, 0, v_nParams_1164_);
lean_closure_set(v___f_1187_, 1, v_numMotives_1179_);
lean_closure_set(v___f_1187_, 2, v_numMinors_1180_);
lean_closure_set(v___f_1187_, 3, v___x_1171_);
lean_closure_set(v___f_1187_, 4, v_head_1185_);
lean_closure_set(v___f_1187_, 5, v_tail_1186_);
lean_closure_set(v___f_1187_, 6, v_recName_1163_);
lean_closure_set(v___f_1187_, 7, v_belowName_1165_);
lean_closure_set(v___f_1187_, 8, v_levelParams_1181_);
v___x_1188_ = 0;
v___x_1189_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1182_, v___f_1187_, v___x_1188_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc_n(v_a_1190_, 2);
lean_dec_ref_known(v___x_1189_, 1);
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v_a_1190_);
v___x_1192_ = v___x_1176_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1190_);
v___x_1192_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_addDecl(v___x_1192_, v___x_1188_, v_a_1168_, v_a_1169_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_toConstantVal_1194_; lean_object* v_name_1195_; lean_object* v___x_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1274_; 
lean_dec_ref_known(v___x_1193_, 1);
v_toConstantVal_1194_ = lean_ctor_get(v_a_1190_, 0);
lean_inc_ref(v_toConstantVal_1194_);
lean_dec(v_a_1190_);
v_name_1195_ = lean_ctor_get(v_toConstantVal_1194_, 0);
lean_inc_n(v_name_1195_, 2);
lean_dec_ref(v_toConstantVal_1194_);
v___x_1196_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1195_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1196_, 0);
lean_dec(v_unused_1275_);
v___x_1198_ = v___x_1196_;
v_isShared_1199_ = v_isSharedCheck_1274_;
goto v_resetjp_1197_;
}
else
{
lean_dec(v___x_1196_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1274_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v_env_1201_; lean_object* v_nextMacroScope_1202_; lean_object* v_ngen_1203_; lean_object* v_auxDeclNGen_1204_; lean_object* v_traceState_1205_; lean_object* v_recordedDeps_1206_; lean_object* v_messages_1207_; lean_object* v_infoState_1208_; lean_object* v_snapshotTasks_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1272_; 
v___x_1200_ = lean_st_ref_take(v_a_1169_);
v_env_1201_ = lean_ctor_get(v___x_1200_, 0);
v_nextMacroScope_1202_ = lean_ctor_get(v___x_1200_, 1);
v_ngen_1203_ = lean_ctor_get(v___x_1200_, 2);
v_auxDeclNGen_1204_ = lean_ctor_get(v___x_1200_, 3);
v_traceState_1205_ = lean_ctor_get(v___x_1200_, 4);
v_recordedDeps_1206_ = lean_ctor_get(v___x_1200_, 6);
v_messages_1207_ = lean_ctor_get(v___x_1200_, 7);
v_infoState_1208_ = lean_ctor_get(v___x_1200_, 8);
v_snapshotTasks_1209_ = lean_ctor_get(v___x_1200_, 9);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1200_, 5);
lean_dec(v_unused_1273_);
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1272_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_snapshotTasks_1209_);
lean_inc(v_infoState_1208_);
lean_inc(v_messages_1207_);
lean_inc(v_recordedDeps_1206_);
lean_inc(v_traceState_1205_);
lean_inc(v_auxDeclNGen_1204_);
lean_inc(v_ngen_1203_);
lean_inc(v_nextMacroScope_1202_);
lean_inc(v_env_1201_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1272_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_inc(v_name_1195_);
v___x_1213_ = l_Lean_markAuxRecursor(v_env_1201_, v_name_1195_);
v___x_1214_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 5, v___x_1214_);
lean_ctor_set(v___x_1211_, 0, v___x_1213_);
v___x_1216_ = v___x_1211_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_nextMacroScope_1202_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_ngen_1203_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_auxDeclNGen_1204_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_traceState_1205_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1271_, 6, v_recordedDeps_1206_);
lean_ctor_set(v_reuseFailAlloc_1271_, 7, v_messages_1207_);
lean_ctor_set(v_reuseFailAlloc_1271_, 8, v_infoState_1208_);
lean_ctor_set(v_reuseFailAlloc_1271_, 9, v_snapshotTasks_1209_);
v___x_1216_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_mctx_1219_; lean_object* v_zetaDeltaFVarIds_1220_; lean_object* v_postponed_1221_; lean_object* v_diag_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1269_; 
v___x_1217_ = lean_st_ref_put(v_a_1169_, v___x_1216_);
v___x_1218_ = lean_st_ref_take(v_a_1167_);
v_mctx_1219_ = lean_ctor_get(v___x_1218_, 0);
v_zetaDeltaFVarIds_1220_ = lean_ctor_get(v___x_1218_, 2);
v_postponed_1221_ = lean_ctor_get(v___x_1218_, 3);
v_diag_1222_ = lean_ctor_get(v___x_1218_, 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1218_, 1);
lean_dec(v_unused_1270_);
v___x_1224_ = v___x_1218_;
v_isShared_1225_ = v_isSharedCheck_1269_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_diag_1222_);
lean_inc(v_postponed_1221_);
lean_inc(v_zetaDeltaFVarIds_1220_);
lean_inc(v_mctx_1219_);
lean_dec(v___x_1218_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1269_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_mctx_1219_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_zetaDeltaFVarIds_1220_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_postponed_1221_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_diag_1222_);
v___x_1228_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v_env_1231_; lean_object* v_nextMacroScope_1232_; lean_object* v_ngen_1233_; lean_object* v_auxDeclNGen_1234_; lean_object* v_traceState_1235_; lean_object* v_recordedDeps_1236_; lean_object* v_messages_1237_; lean_object* v_infoState_1238_; lean_object* v_snapshotTasks_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1266_; 
v___x_1229_ = lean_st_ref_put(v_a_1167_, v___x_1228_);
v___x_1230_ = lean_st_ref_take(v_a_1169_);
v_env_1231_ = lean_ctor_get(v___x_1230_, 0);
v_nextMacroScope_1232_ = lean_ctor_get(v___x_1230_, 1);
v_ngen_1233_ = lean_ctor_get(v___x_1230_, 2);
v_auxDeclNGen_1234_ = lean_ctor_get(v___x_1230_, 3);
v_traceState_1235_ = lean_ctor_get(v___x_1230_, 4);
v_recordedDeps_1236_ = lean_ctor_get(v___x_1230_, 6);
v_messages_1237_ = lean_ctor_get(v___x_1230_, 7);
v_infoState_1238_ = lean_ctor_get(v___x_1230_, 8);
v_snapshotTasks_1239_ = lean_ctor_get(v___x_1230_, 9);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1230_, 5);
lean_dec(v_unused_1267_);
v___x_1241_ = v___x_1230_;
v_isShared_1242_ = v_isSharedCheck_1266_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snapshotTasks_1239_);
lean_inc(v_infoState_1238_);
lean_inc(v_messages_1237_);
lean_inc(v_recordedDeps_1236_);
lean_inc(v_traceState_1235_);
lean_inc(v_auxDeclNGen_1234_);
lean_inc(v_ngen_1233_);
lean_inc(v_nextMacroScope_1232_);
lean_inc(v_env_1231_);
lean_dec(v___x_1230_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1266_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = l_Lean_addProtected(v_env_1231_, v_name_1195_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 5, v___x_1214_);
lean_ctor_set(v___x_1241_, 0, v___x_1243_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_nextMacroScope_1232_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_ngen_1233_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_auxDeclNGen_1234_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_traceState_1235_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_recordedDeps_1236_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_messages_1237_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_infoState_1238_);
lean_ctor_set(v_reuseFailAlloc_1265_, 9, v_snapshotTasks_1239_);
v___x_1245_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v_mctx_1248_; lean_object* v_zetaDeltaFVarIds_1249_; lean_object* v_postponed_1250_; lean_object* v_diag_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1263_; 
v___x_1246_ = lean_st_ref_put(v_a_1169_, v___x_1245_);
v___x_1247_ = lean_st_ref_take(v_a_1167_);
v_mctx_1248_ = lean_ctor_get(v___x_1247_, 0);
v_zetaDeltaFVarIds_1249_ = lean_ctor_get(v___x_1247_, 2);
v_postponed_1250_ = lean_ctor_get(v___x_1247_, 3);
v_diag_1251_ = lean_ctor_get(v___x_1247_, 4);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1247_, 1);
lean_dec(v_unused_1264_);
v___x_1253_ = v___x_1247_;
v_isShared_1254_ = v_isSharedCheck_1263_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_diag_1251_);
lean_inc(v_postponed_1250_);
lean_inc(v_zetaDeltaFVarIds_1249_);
lean_inc(v_mctx_1248_);
lean_dec(v___x_1247_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1263_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_box(0);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1226_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_mctx_1248_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_zetaDeltaFVarIds_1249_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_postponed_1250_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_diag_1251_);
v___x_1257_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_st_ref_put(v_a_1167_, v___x_1257_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1255_);
v___x_1260_ = v___x_1198_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
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
lean_dec(v_a_1190_);
return v___x_1193_;
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_del_object(v___x_1176_);
v_a_1277_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1189_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1189_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec(v___x_1184_);
lean_dec_ref(v_type_1182_);
lean_dec(v_levelParams_1181_);
lean_dec(v_numMinors_1180_);
lean_dec(v_numMotives_1179_);
lean_del_object(v___x_1176_);
lean_dec(v_belowName_1165_);
lean_dec(v_nParams_1164_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1286_ = l_Lean_MessageData_ofName(v_recName_1163_);
v___x_1287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1289_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1290_;
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_dec(v_a_1173_);
lean_dec(v_belowName_1165_);
lean_dec(v_nParams_1164_);
v___x_1292_ = l_Lean_MessageData_ofName(v_recName_1163_);
v___x_1293_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1292_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1294_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
return v___x_1295_;
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_belowName_1165_);
lean_dec(v_nParams_1164_);
lean_dec(v_recName_1163_);
v_a_1296_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1172_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1172_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1304_, lean_object* v_nParams_1305_, lean_object* v_belowName_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1304_, v_nParams_1305_, v_belowName_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1313_, lean_object* v_msg_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_msg_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1321_, v_msg_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11(lean_object* v_00_u03b2_1329_){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg(){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg___boxed(lean_object* v___dummy_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg();
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8(lean_object* v_00_u03b2_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1337_, lean_object* v_constName_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_constName_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1345_, v_constName_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1353_, uint8_t v_s_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1353_, v_s_1354_, v___y_1356_, v___y_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1361_, lean_object* v_s_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
uint8_t v_s_boxed_1368_; lean_object* v_res_1369_; 
v_s_boxed_1368_ = lean_unbox(v_s_1362_);
v_res_1369_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1361_, v_s_boxed_1368_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1370_, lean_object* v_ref_1371_, lean_object* v_constName_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1371_, v_constName_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_ref_1380_, lean_object* v_constName_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1379_, v_ref_1380_, v_constName_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v_ref_1380_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_msg_1390_, lean_object* v_declHint_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1389_, v_msg_1390_, v_declHint_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_ref_1399_, lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(v_00_u03b1_1398_, v_ref_1399_, v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v_ref_1399_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(lean_object* v_msg_1408_, lean_object* v_declHint_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1408_, v_declHint_1409_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_1416_, lean_object* v_declHint_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(v_msg_1416_, v_declHint_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(lean_object* v_00_u03b1_1424_, lean_object* v_ref_1425_, lean_object* v_msg_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1425_, v_msg_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_ref_1434_, lean_object* v_msg_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(v_00_u03b1_1433_, v_ref_1434_, v_msg_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v_ref_1434_);
return v_res_1441_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(32u);
v___x_1443_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1445_ = ((size_t)5ULL);
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = lean_unsigned_to_nat(32u);
v___x_1448_ = lean_mk_empty_array_with_capacity(v___x_1447_);
v___x_1449_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1450_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___x_1448_);
lean_ctor_set(v___x_1450_, 2, v___x_1446_);
lean_ctor_set(v___x_1450_, 3, v___x_1446_);
lean_ctor_set_usize(v___x_1450_, 4, v___x_1445_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; lean_object* v_traceState_1454_; lean_object* v_traces_1455_; lean_object* v___x_1456_; lean_object* v_traceState_1457_; lean_object* v_env_1458_; lean_object* v_nextMacroScope_1459_; lean_object* v_ngen_1460_; lean_object* v_auxDeclNGen_1461_; lean_object* v_cache_1462_; lean_object* v_recordedDeps_1463_; lean_object* v_messages_1464_; lean_object* v_infoState_1465_; lean_object* v_snapshotTasks_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1485_; 
v___x_1453_ = lean_st_ref_get(v___y_1451_);
v_traceState_1454_ = lean_ctor_get(v___x_1453_, 4);
lean_inc_ref(v_traceState_1454_);
lean_dec(v___x_1453_);
v_traces_1455_ = lean_ctor_get(v_traceState_1454_, 0);
lean_inc_ref(v_traces_1455_);
lean_dec_ref(v_traceState_1454_);
v___x_1456_ = lean_st_ref_take(v___y_1451_);
v_traceState_1457_ = lean_ctor_get(v___x_1456_, 4);
v_env_1458_ = lean_ctor_get(v___x_1456_, 0);
v_nextMacroScope_1459_ = lean_ctor_get(v___x_1456_, 1);
v_ngen_1460_ = lean_ctor_get(v___x_1456_, 2);
v_auxDeclNGen_1461_ = lean_ctor_get(v___x_1456_, 3);
v_cache_1462_ = lean_ctor_get(v___x_1456_, 5);
v_recordedDeps_1463_ = lean_ctor_get(v___x_1456_, 6);
v_messages_1464_ = lean_ctor_get(v___x_1456_, 7);
v_infoState_1465_ = lean_ctor_get(v___x_1456_, 8);
v_snapshotTasks_1466_ = lean_ctor_get(v___x_1456_, 9);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1468_ = v___x_1456_;
v_isShared_1469_ = v_isSharedCheck_1485_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_snapshotTasks_1466_);
lean_inc(v_infoState_1465_);
lean_inc(v_messages_1464_);
lean_inc(v_recordedDeps_1463_);
lean_inc(v_cache_1462_);
lean_inc(v_traceState_1457_);
lean_inc(v_auxDeclNGen_1461_);
lean_inc(v_ngen_1460_);
lean_inc(v_nextMacroScope_1459_);
lean_inc(v_env_1458_);
lean_dec(v___x_1456_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1485_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
uint64_t v_tid_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1483_; 
v_tid_1470_ = lean_ctor_get_uint64(v_traceState_1457_, sizeof(void*)*1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_traceState_1457_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_traceState_1457_, 0);
lean_dec(v_unused_1484_);
v___x_1472_ = v_traceState_1457_;
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
else
{
lean_dec(v_traceState_1457_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1483_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1474_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1474_);
v___x_1476_ = v___x_1472_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1474_);
lean_ctor_set_uint64(v_reuseFailAlloc_1482_, sizeof(void*)*1, v_tid_1470_);
v___x_1476_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1478_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 4, v___x_1476_);
v___x_1478_ = v___x_1468_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_env_1458_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_nextMacroScope_1459_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_ngen_1460_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_auxDeclNGen_1461_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1481_, 5, v_cache_1462_);
lean_ctor_set(v_reuseFailAlloc_1481_, 6, v_recordedDeps_1463_);
lean_ctor_set(v_reuseFailAlloc_1481_, 7, v_messages_1464_);
lean_ctor_set(v_reuseFailAlloc_1481_, 8, v_infoState_1465_);
lean_ctor_set(v_reuseFailAlloc_1481_, 9, v_snapshotTasks_1466_);
v___x_1478_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_st_ref_put(v___y_1451_, v___x_1478_);
v___x_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_traces_1455_);
return v___x_1480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1486_);
lean_dec(v___y_1486_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1501_, lean_object* v_opt_1502_){
_start:
{
lean_object* v_name_1503_; lean_object* v_defValue_1504_; lean_object* v_map_1505_; lean_object* v___x_1506_; 
v_name_1503_ = lean_ctor_get(v_opt_1502_, 0);
v_defValue_1504_ = lean_ctor_get(v_opt_1502_, 1);
v_map_1505_ = lean_ctor_get(v_opts_1501_, 0);
v___x_1506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1505_, v_name_1503_);
if (lean_obj_tag(v___x_1506_) == 0)
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_unbox(v_defValue_1504_);
return v___x_1507_;
}
else
{
lean_object* v_val_1508_; 
v_val_1508_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v___x_1506_, 1);
if (lean_obj_tag(v_val_1508_) == 1)
{
uint8_t v_v_1509_; 
v_v_1509_ = lean_ctor_get_uint8(v_val_1508_, 0);
lean_dec_ref_known(v_val_1508_, 0);
return v_v_1509_;
}
else
{
uint8_t v___x_1510_; 
lean_dec(v_val_1508_);
v___x_1510_ = lean_unbox(v_defValue_1504_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1511_, lean_object* v_opt_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1511_, v_opt_1512_);
lean_dec_ref(v_opt_1512_);
lean_dec_ref(v_opts_1511_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1515_, lean_object* v_x_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = l_Lean_MessageData_ofName(v_indName_1515_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1524_, lean_object* v_x_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_mkBelow___lam__0(v_indName_1524_, v_x_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec_ref(v_x_1525_);
return v_res_1531_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1532_){
_start:
{
if (lean_obj_tag(v_e_1532_) == 0)
{
uint8_t v___x_1533_; 
v___x_1533_ = 2;
return v___x_1533_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1535_);
lean_dec_ref(v_e_1535_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1538_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v_x_1538_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v_x_1538_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v_x_1538_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 1);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v_a_1548_ = lean_ctor_get(v_x_1538_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v_x_1538_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v_x_1538_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 0);
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1559_, lean_object* v_opt_1560_){
_start:
{
lean_object* v_name_1561_; lean_object* v_defValue_1562_; lean_object* v_map_1563_; lean_object* v___x_1564_; 
v_name_1561_ = lean_ctor_get(v_opt_1560_, 0);
v_defValue_1562_ = lean_ctor_get(v_opt_1560_, 1);
v_map_1563_ = lean_ctor_get(v_opts_1559_, 0);
v___x_1564_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1563_, v_name_1561_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_inc(v_defValue_1562_);
return v_defValue_1562_;
}
else
{
lean_object* v_val_1565_; 
v_val_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_val_1565_);
lean_dec_ref_known(v___x_1564_, 1);
if (lean_obj_tag(v_val_1565_) == 3)
{
lean_object* v_v_1566_; 
v_v_1566_ = lean_ctor_get(v_val_1565_, 0);
lean_inc(v_v_1566_);
lean_dec_ref_known(v_val_1565_, 1);
return v_v_1566_;
}
else
{
lean_dec(v_val_1565_);
lean_inc(v_defValue_1562_);
return v_defValue_1562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1567_, lean_object* v_opt_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1567_, v_opt_1568_);
lean_dec_ref(v_opt_1568_);
lean_dec_ref(v_opts_1567_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1570_, size_t v_i_1571_, lean_object* v_bs_1572_){
_start:
{
uint8_t v___x_1573_; 
v___x_1573_ = lean_usize_dec_lt(v_i_1571_, v_sz_1570_);
if (v___x_1573_ == 0)
{
return v_bs_1572_;
}
else
{
lean_object* v_v_1574_; lean_object* v_msg_1575_; lean_object* v___x_1576_; lean_object* v_bs_x27_1577_; size_t v___x_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
v_v_1574_ = lean_array_uget_borrowed(v_bs_1572_, v_i_1571_);
v_msg_1575_ = lean_ctor_get(v_v_1574_, 1);
lean_inc_ref(v_msg_1575_);
v___x_1576_ = lean_unsigned_to_nat(0u);
v_bs_x27_1577_ = lean_array_uset(v_bs_1572_, v_i_1571_, v___x_1576_);
v___x_1578_ = ((size_t)1ULL);
v___x_1579_ = lean_usize_add(v_i_1571_, v___x_1578_);
v___x_1580_ = lean_array_uset(v_bs_x27_1577_, v_i_1571_, v_msg_1575_);
v_i_1571_ = v___x_1579_;
v_bs_1572_ = v___x_1580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1582_, lean_object* v_i_1583_, lean_object* v_bs_1584_){
_start:
{
size_t v_sz_boxed_1585_; size_t v_i_boxed_1586_; lean_object* v_res_1587_; 
v_sz_boxed_1585_ = lean_unbox_usize(v_sz_1582_);
lean_dec(v_sz_1582_);
v_i_boxed_1586_ = lean_unbox_usize(v_i_1583_);
lean_dec(v_i_1583_);
v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1585_, v_i_boxed_1586_, v_bs_1584_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1588_, lean_object* v_data_1589_, lean_object* v_ref_1590_, lean_object* v_msg_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_toCold_1597_; lean_object* v_currRecDepth_1598_; lean_object* v_ref_1599_; uint16_t v_optionFlags_1600_; uint8_t v_suppressElabErrors_1601_; uint8_t v_checkDeprecated_1602_; uint8_t v_isRecordingDeps_1603_; lean_object* v_ref_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v_traceState_1607_; lean_object* v_traces_1608_; lean_object* v___x_1609_; size_t v_sz_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v_msg_1613_; lean_object* v___x_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1653_; 
v_toCold_1597_ = lean_ctor_get(v___y_1594_, 0);
v_currRecDepth_1598_ = lean_ctor_get(v___y_1594_, 1);
v_ref_1599_ = lean_ctor_get(v___y_1594_, 2);
v_optionFlags_1600_ = lean_ctor_get_uint16(v___y_1594_, sizeof(void*)*3);
v_suppressElabErrors_1601_ = lean_ctor_get_uint8(v___y_1594_, sizeof(void*)*3 + 2);
v_checkDeprecated_1602_ = lean_ctor_get_uint8(v___y_1594_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1603_ = lean_ctor_get_uint8(v___y_1594_, sizeof(void*)*3 + 4);
v_ref_1604_ = l_Lean_replaceRef(v_ref_1590_, v_ref_1599_);
lean_inc(v_currRecDepth_1598_);
lean_inc_ref(v_toCold_1597_);
v___x_1605_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1605_, 0, v_toCold_1597_);
lean_ctor_set(v___x_1605_, 1, v_currRecDepth_1598_);
lean_ctor_set(v___x_1605_, 2, v_ref_1604_);
lean_ctor_set_uint16(v___x_1605_, sizeof(void*)*3, v_optionFlags_1600_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*3 + 2, v_suppressElabErrors_1601_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*3 + 3, v_checkDeprecated_1602_);
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*3 + 4, v_isRecordingDeps_1603_);
v___x_1606_ = lean_st_ref_get(v___y_1595_);
v_traceState_1607_ = lean_ctor_get(v___x_1606_, 4);
lean_inc_ref(v_traceState_1607_);
lean_dec(v___x_1606_);
v_traces_1608_ = lean_ctor_get(v_traceState_1607_, 0);
lean_inc_ref(v_traces_1608_);
lean_dec_ref(v_traceState_1607_);
v___x_1609_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1608_);
lean_dec_ref(v_traces_1608_);
v_sz_1610_ = lean_array_size(v___x_1609_);
v___x_1611_ = ((size_t)0ULL);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1610_, v___x_1611_, v___x_1609_);
v_msg_1613_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1613_, 0, v_data_1589_);
lean_ctor_set(v_msg_1613_, 1, v_msg_1591_);
lean_ctor_set(v_msg_1613_, 2, v___x_1612_);
v___x_1614_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1613_, v___y_1592_, v___y_1593_, v___x_1605_, v___y_1595_);
lean_dec_ref_known(v___x_1605_, 3);
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1653_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1653_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v_traceState_1620_; lean_object* v_env_1621_; lean_object* v_nextMacroScope_1622_; lean_object* v_ngen_1623_; lean_object* v_auxDeclNGen_1624_; lean_object* v_cache_1625_; lean_object* v_recordedDeps_1626_; lean_object* v_messages_1627_; lean_object* v_infoState_1628_; lean_object* v_snapshotTasks_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1652_; 
v___x_1619_ = lean_st_ref_take(v___y_1595_);
v_traceState_1620_ = lean_ctor_get(v___x_1619_, 4);
v_env_1621_ = lean_ctor_get(v___x_1619_, 0);
v_nextMacroScope_1622_ = lean_ctor_get(v___x_1619_, 1);
v_ngen_1623_ = lean_ctor_get(v___x_1619_, 2);
v_auxDeclNGen_1624_ = lean_ctor_get(v___x_1619_, 3);
v_cache_1625_ = lean_ctor_get(v___x_1619_, 5);
v_recordedDeps_1626_ = lean_ctor_get(v___x_1619_, 6);
v_messages_1627_ = lean_ctor_get(v___x_1619_, 7);
v_infoState_1628_ = lean_ctor_get(v___x_1619_, 8);
v_snapshotTasks_1629_ = lean_ctor_get(v___x_1619_, 9);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1631_ = v___x_1619_;
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_snapshotTasks_1629_);
lean_inc(v_infoState_1628_);
lean_inc(v_messages_1627_);
lean_inc(v_recordedDeps_1626_);
lean_inc(v_cache_1625_);
lean_inc(v_traceState_1620_);
lean_inc(v_auxDeclNGen_1624_);
lean_inc(v_ngen_1623_);
lean_inc(v_nextMacroScope_1622_);
lean_inc(v_env_1621_);
lean_dec(v___x_1619_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1652_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
uint64_t v_tid_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1650_; 
v_tid_1633_ = lean_ctor_get_uint64(v_traceState_1620_, sizeof(void*)*1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_traceState_1620_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v_traceState_1620_, 0);
lean_dec(v_unused_1651_);
v___x_1635_ = v_traceState_1620_;
v_isShared_1636_ = v_isSharedCheck_1650_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_traceState_1620_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1650_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_ref_1590_);
lean_ctor_set(v___x_1638_, 1, v_a_1615_);
v___x_1639_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1588_, v___x_1638_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1639_);
v___x_1641_ = v___x_1635_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1639_);
lean_ctor_set_uint64(v_reuseFailAlloc_1649_, sizeof(void*)*1, v_tid_1633_);
v___x_1641_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v___x_1641_);
v___x_1643_ = v___x_1631_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_env_1621_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_nextMacroScope_1622_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_ngen_1623_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_auxDeclNGen_1624_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1648_, 5, v_cache_1625_);
lean_ctor_set(v_reuseFailAlloc_1648_, 6, v_recordedDeps_1626_);
lean_ctor_set(v_reuseFailAlloc_1648_, 7, v_messages_1627_);
lean_ctor_set(v_reuseFailAlloc_1648_, 8, v_infoState_1628_);
lean_ctor_set(v_reuseFailAlloc_1648_, 9, v_snapshotTasks_1629_);
v___x_1643_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_st_ref_put(v___y_1595_, v___x_1643_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1637_);
v___x_1646_ = v___x_1617_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1637_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1654_, lean_object* v_data_1655_, lean_object* v_ref_1656_, lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1654_, v_data_1655_, v_ref_1656_, v_msg_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1663_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1664_; double v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_float_of_nat(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1668_ = l_Lean_stringToMessageData(v___x_1667_);
return v___x_1668_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1669_; double v___x_1670_; 
v___x_1669_ = lean_unsigned_to_nat(1000u);
v___x_1670_ = lean_float_of_nat(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1671_, uint8_t v_collapsed_1672_, lean_object* v_tag_1673_, lean_object* v_opts_1674_, uint8_t v_clsEnabled_1675_, lean_object* v_oldTraces_1676_, lean_object* v_msg_1677_, lean_object* v_resStartStop_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v_data_1689_; lean_object* v_fst_1692_; lean_object* v_snd_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___y_1697_; lean_object* v_a_1698_; uint8_t v___y_1713_; double v___y_1745_; 
v_fst_1684_ = lean_ctor_get(v_resStartStop_1678_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v_resStartStop_1678_, 1);
lean_inc(v_snd_1685_);
lean_dec_ref(v_resStartStop_1678_);
v_fst_1692_ = lean_ctor_get(v_snd_1685_, 0);
lean_inc(v_fst_1692_);
v_snd_1693_ = lean_ctor_get(v_snd_1685_, 1);
lean_inc(v_snd_1693_);
lean_dec(v_snd_1685_);
v___x_1694_ = l_Lean_trace_profiler;
v___x_1695_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1674_, v___x_1694_);
if (v___x_1695_ == 0)
{
v___y_1713_ = v___x_1695_;
goto v___jp_1712_;
}
else
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1751_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1674_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; double v___x_1754_; double v___x_1755_; double v___x_1756_; 
v___x_1752_ = l_Lean_trace_profiler_threshold;
v___x_1753_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1674_, v___x_1752_);
v___x_1754_ = lean_float_of_nat(v___x_1753_);
v___x_1755_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1756_ = lean_float_div(v___x_1754_, v___x_1755_);
v___y_1745_ = v___x_1756_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; double v___x_1759_; 
v___x_1757_ = l_Lean_trace_profiler_threshold;
v___x_1758_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1674_, v___x_1757_);
v___x_1759_ = lean_float_of_nat(v___x_1758_);
v___y_1745_ = v___x_1759_;
goto v___jp_1744_;
}
}
v___jp_1686_:
{
lean_object* v___x_1690_; 
lean_inc(v___y_1688_);
v___x_1690_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1676_, v_data_1689_, v___y_1688_, v___y_1687_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1691_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1684_);
return v___x_1691_;
}
else
{
lean_dec(v_fst_1684_);
return v___x_1690_;
}
}
v___jp_1696_:
{
uint8_t v_result_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; double v___x_1702_; lean_object* v_data_1703_; 
v_result_1699_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1684_);
v___x_1700_ = lean_box(v_result_1699_);
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
v___x_1702_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1673_);
lean_inc_ref(v___x_1701_);
lean_inc(v_cls_1671_);
v_data_1703_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1703_, 0, v_cls_1671_);
lean_ctor_set(v_data_1703_, 1, v___x_1701_);
lean_ctor_set(v_data_1703_, 2, v_tag_1673_);
lean_ctor_set_float(v_data_1703_, sizeof(void*)*3, v___x_1702_);
lean_ctor_set_float(v_data_1703_, sizeof(void*)*3 + 8, v___x_1702_);
lean_ctor_set_uint8(v_data_1703_, sizeof(void*)*3 + 16, v_collapsed_1672_);
if (v___x_1695_ == 0)
{
lean_dec_ref_known(v___x_1701_, 1);
lean_dec(v_snd_1693_);
lean_dec(v_fst_1692_);
lean_dec_ref(v_tag_1673_);
lean_dec(v_cls_1671_);
v___y_1687_ = v_a_1698_;
v___y_1688_ = v___y_1697_;
v_data_1689_ = v_data_1703_;
goto v___jp_1686_;
}
else
{
lean_object* v_data_1704_; double v___x_1705_; double v___x_1706_; 
lean_dec_ref_known(v_data_1703_, 3);
v_data_1704_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1704_, 0, v_cls_1671_);
lean_ctor_set(v_data_1704_, 1, v___x_1701_);
lean_ctor_set(v_data_1704_, 2, v_tag_1673_);
v___x_1705_ = lean_unbox_float(v_fst_1692_);
lean_dec(v_fst_1692_);
lean_ctor_set_float(v_data_1704_, sizeof(void*)*3, v___x_1705_);
v___x_1706_ = lean_unbox_float(v_snd_1693_);
lean_dec(v_snd_1693_);
lean_ctor_set_float(v_data_1704_, sizeof(void*)*3 + 8, v___x_1706_);
lean_ctor_set_uint8(v_data_1704_, sizeof(void*)*3 + 16, v_collapsed_1672_);
v___y_1687_ = v_a_1698_;
v___y_1688_ = v___y_1697_;
v_data_1689_ = v_data_1704_;
goto v___jp_1686_;
}
}
v___jp_1707_:
{
lean_object* v_ref_1708_; lean_object* v___x_1709_; 
v_ref_1708_ = lean_ctor_get(v___y_1681_, 2);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v_fst_1684_);
v___x_1709_ = lean_apply_6(v_msg_1677_, v_fst_1684_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, lean_box(0));
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v___y_1697_ = v_ref_1708_;
v_a_1698_ = v_a_1710_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref_known(v___x_1709_, 1);
v___x_1711_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1697_ = v_ref_1708_;
v_a_1698_ = v___x_1711_;
goto v___jp_1696_;
}
}
v___jp_1712_:
{
if (v_clsEnabled_1675_ == 0)
{
if (v___y_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v_traceState_1715_; lean_object* v_env_1716_; lean_object* v_nextMacroScope_1717_; lean_object* v_ngen_1718_; lean_object* v_auxDeclNGen_1719_; lean_object* v_cache_1720_; lean_object* v_recordedDeps_1721_; lean_object* v_messages_1722_; lean_object* v_infoState_1723_; lean_object* v_snapshotTasks_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_snd_1693_);
lean_dec(v_fst_1692_);
lean_dec_ref(v_msg_1677_);
lean_dec_ref(v_tag_1673_);
lean_dec(v_cls_1671_);
v___x_1714_ = lean_st_ref_take(v___y_1682_);
v_traceState_1715_ = lean_ctor_get(v___x_1714_, 4);
v_env_1716_ = lean_ctor_get(v___x_1714_, 0);
v_nextMacroScope_1717_ = lean_ctor_get(v___x_1714_, 1);
v_ngen_1718_ = lean_ctor_get(v___x_1714_, 2);
v_auxDeclNGen_1719_ = lean_ctor_get(v___x_1714_, 3);
v_cache_1720_ = lean_ctor_get(v___x_1714_, 5);
v_recordedDeps_1721_ = lean_ctor_get(v___x_1714_, 6);
v_messages_1722_ = lean_ctor_get(v___x_1714_, 7);
v_infoState_1723_ = lean_ctor_get(v___x_1714_, 8);
v_snapshotTasks_1724_ = lean_ctor_get(v___x_1714_, 9);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1726_ = v___x_1714_;
v_isShared_1727_ = v_isSharedCheck_1743_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snapshotTasks_1724_);
lean_inc(v_infoState_1723_);
lean_inc(v_messages_1722_);
lean_inc(v_recordedDeps_1721_);
lean_inc(v_cache_1720_);
lean_inc(v_traceState_1715_);
lean_inc(v_auxDeclNGen_1719_);
lean_inc(v_ngen_1718_);
lean_inc(v_nextMacroScope_1717_);
lean_inc(v_env_1716_);
lean_dec(v___x_1714_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1743_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
uint64_t v_tid_1728_; lean_object* v_traces_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1742_; 
v_tid_1728_ = lean_ctor_get_uint64(v_traceState_1715_, sizeof(void*)*1);
v_traces_1729_ = lean_ctor_get(v_traceState_1715_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_traceState_1715_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1731_ = v_traceState_1715_;
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_traces_1729_);
lean_dec(v_traceState_1715_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1742_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1676_, v_traces_1729_);
lean_dec_ref(v_traces_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1733_);
lean_ctor_set_uint64(v_reuseFailAlloc_1741_, sizeof(void*)*1, v_tid_1728_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 4, v___x_1735_);
v___x_1737_ = v___x_1726_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_env_1716_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_nextMacroScope_1717_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_ngen_1718_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_auxDeclNGen_1719_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1740_, 5, v_cache_1720_);
lean_ctor_set(v_reuseFailAlloc_1740_, 6, v_recordedDeps_1721_);
lean_ctor_set(v_reuseFailAlloc_1740_, 7, v_messages_1722_);
lean_ctor_set(v_reuseFailAlloc_1740_, 8, v_infoState_1723_);
lean_ctor_set(v_reuseFailAlloc_1740_, 9, v_snapshotTasks_1724_);
v___x_1737_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = lean_st_ref_put(v___y_1682_, v___x_1737_);
v___x_1739_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1684_);
return v___x_1739_;
}
}
}
}
}
else
{
goto v___jp_1707_;
}
}
else
{
goto v___jp_1707_;
}
}
v___jp_1744_:
{
double v___x_1746_; double v___x_1747_; double v___x_1748_; uint8_t v___x_1749_; 
v___x_1746_ = lean_unbox_float(v_snd_1693_);
v___x_1747_ = lean_unbox_float(v_fst_1692_);
v___x_1748_ = lean_float_sub(v___x_1746_, v___x_1747_);
v___x_1749_ = lean_float_decLt(v___y_1745_, v___x_1748_);
v___y_1713_ = v___x_1749_;
goto v___jp_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1760_, lean_object* v_collapsed_1761_, lean_object* v_tag_1762_, lean_object* v_opts_1763_, lean_object* v_clsEnabled_1764_, lean_object* v_oldTraces_1765_, lean_object* v_msg_1766_, lean_object* v_resStartStop_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v_collapsed_boxed_1773_; uint8_t v_clsEnabled_boxed_1774_; lean_object* v_res_1775_; 
v_collapsed_boxed_1773_ = lean_unbox(v_collapsed_1761_);
v_clsEnabled_boxed_1774_ = lean_unbox(v_clsEnabled_1764_);
v_res_1775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1760_, v_collapsed_boxed_1773_, v_tag_1762_, v_opts_1763_, v_clsEnabled_boxed_1774_, v_oldTraces_1765_, v_msg_1766_, v_resStartStop_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec_ref(v_opts_1763_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1776_, lean_object* v___x_1777_, lean_object* v___x_1778_, lean_object* v___x_1779_, lean_object* v_a_1780_, lean_object* v_b_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
uint8_t v___x_1787_; 
v___x_1787_ = lean_nat_dec_lt(v_a_1780_, v_upperBound_1776_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
lean_dec(v_a_1780_);
lean_dec(v___x_1779_);
lean_dec(v___x_1778_);
lean_dec(v___x_1777_);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_b_1781_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = lean_nat_add(v_a_1780_, v___x_1790_);
lean_dec(v_a_1780_);
lean_inc_n(v___x_1791_, 2);
lean_inc(v___x_1777_);
v___x_1792_ = lean_name_append_index_after(v___x_1777_, v___x_1791_);
lean_inc(v___x_1778_);
v___x_1793_ = lean_name_append_index_after(v___x_1778_, v___x_1791_);
lean_inc(v___x_1779_);
v___x_1794_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1792_, v___x_1779_, v___x_1793_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref_known(v___x_1794_, 1);
v_a_1780_ = v___x_1791_;
v_b_1781_ = v___x_1789_;
goto _start;
}
else
{
lean_dec(v___x_1791_);
lean_dec(v___x_1779_);
lean_dec(v___x_1778_);
lean_dec(v___x_1777_);
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v___x_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v_a_1800_, v_b_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v_upperBound_1796_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1818_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1819_ = l_Lean_Name_append(v___x_1818_, v___x_1817_);
return v___x_1819_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1820_; double v___x_1821_; 
v___x_1820_ = lean_unsigned_to_nat(1000000000u);
v___x_1821_ = lean_float_of_nat(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_toCold_1828_; lean_object* v_options_1829_; lean_object* v_inheritedTraceOptions_1830_; uint8_t v_hasTrace_1831_; lean_object* v___x_1832_; 
v_toCold_1828_ = lean_ctor_get(v_a_1825_, 0);
v_options_1829_ = lean_ctor_get(v_toCold_1828_, 2);
v_inheritedTraceOptions_1830_ = lean_ctor_get(v_toCold_1828_, 11);
v_hasTrace_1831_ = lean_ctor_get_uint8(v_options_1829_, sizeof(void*)*1);
v___x_1832_ = lean_box(0);
if (v_hasTrace_1831_ == 0)
{
lean_object* v___x_1833_; 
lean_inc(v_indName_1822_);
v___x_1833_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1897_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1897_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1897_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
if (lean_obj_tag(v_a_1834_) == 5)
{
lean_object* v_val_1838_; uint8_t v_isRec_1839_; 
v_val_1838_ = lean_ctor_get(v_a_1834_, 0);
lean_inc_ref(v_val_1838_);
lean_dec_ref_known(v_a_1834_, 1);
v_isRec_1839_ = lean_ctor_get_uint8(v_val_1838_, sizeof(void*)*6);
if (v_isRec_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec_ref(v_val_1838_);
lean_dec(v_indName_1822_);
v___x_1840_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1840_);
v___x_1842_ = v___x_1836_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v_toConstantVal_1844_; lean_object* v_numParams_1845_; lean_object* v_all_1846_; lean_object* v_numNested_1847_; lean_object* v_type_1848_; lean_object* v___x_1849_; 
lean_del_object(v___x_1836_);
v_toConstantVal_1844_ = lean_ctor_get(v_val_1838_, 0);
lean_inc_ref(v_toConstantVal_1844_);
v_numParams_1845_ = lean_ctor_get(v_val_1838_, 1);
lean_inc(v_numParams_1845_);
v_all_1846_ = lean_ctor_get(v_val_1838_, 3);
lean_inc(v_all_1846_);
v_numNested_1847_ = lean_ctor_get(v_val_1838_, 5);
lean_inc(v_numNested_1847_);
lean_dec_ref(v_val_1838_);
v_type_1848_ = lean_ctor_get(v_toConstantVal_1844_, 2);
lean_inc_ref(v_type_1848_);
lean_dec_ref(v_toConstantVal_1844_);
v___x_1849_ = l_Lean_Meta_isPropFormerType(v_type_1848_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1884_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1884_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1884_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_unbox(v_a_1850_);
lean_dec(v_a_1850_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_del_object(v___x_1852_);
lean_inc_n(v_indName_1822_, 2);
v___x_1855_ = l_Lean_mkRecName(v_indName_1822_);
v___x_1856_ = l_Lean_mkBelowName(v_indName_1822_);
lean_inc(v___x_1856_);
lean_inc(v_numParams_1845_);
lean_inc(v___x_1855_);
v___x_1857_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1855_, v_numParams_1845_, v___x_1856_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1878_; 
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; 
v_unused_1879_ = lean_ctor_get(v___x_1857_, 0);
lean_dec(v_unused_1879_);
v___x_1859_ = v___x_1857_;
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v___x_1857_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1878_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = l_List_get_x21Internal___redArg(v___x_1832_, v_all_1846_, v___x_1861_);
lean_dec(v_all_1846_);
v___x_1863_ = lean_name_eq(v___x_1862_, v_indName_1822_);
lean_dec(v_indName_1822_);
lean_dec(v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v___x_1856_);
lean_dec(v___x_1855_);
lean_dec(v_numNested_1847_);
lean_dec(v_numParams_1845_);
v___x_1864_ = lean_box(0);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1866_ = v___x_1859_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_del_object(v___x_1859_);
v___x_1868_ = lean_box(0);
v___x_1869_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1847_, v___x_1855_, v___x_1856_, v_numParams_1845_, v___x_1861_, v___x_1868_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_numNested_1847_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; 
v_unused_1877_ = lean_ctor_get(v___x_1869_, 0);
lean_dec(v_unused_1877_);
v___x_1871_ = v___x_1869_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_dec(v___x_1869_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1868_);
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1868_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
return v___x_1869_;
}
}
}
}
else
{
lean_dec(v___x_1856_);
lean_dec(v___x_1855_);
lean_dec(v_numNested_1847_);
lean_dec(v_all_1846_);
lean_dec(v_numParams_1845_);
lean_dec(v_indName_1822_);
return v___x_1857_;
}
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1882_; 
lean_dec(v_numNested_1847_);
lean_dec(v_all_1846_);
lean_dec(v_numParams_1845_);
lean_dec(v_indName_1822_);
v___x_1880_ = lean_box(0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1880_);
v___x_1882_ = v___x_1852_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
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
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_numNested_1847_);
lean_dec(v_all_1846_);
lean_dec(v_numParams_1845_);
lean_dec(v_indName_1822_);
v_a_1885_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1849_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1849_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_a_1834_);
lean_dec(v_indName_1822_);
v___x_1893_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1893_);
v___x_1895_ = v___x_1836_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_indName_1822_);
v_a_1898_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1833_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1833_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_a_1914_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v_a_1929_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_a_1934_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v_a_1939_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_a_1951_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v_a_1956_; 
lean_inc(v_indName_1822_);
v___f_1906_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1906_, 0, v_indName_1822_);
v___x_1907_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1908_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1909_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1830_, v_options_1829_, v___x_1909_);
if (v___x_1910_ == 0)
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = l_Lean_trace_profiler;
v___x_2022_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1829_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_dec_ref(v___f_1906_);
lean_inc(v_indName_1822_);
v___x_2023_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2087_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2087_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2087_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
if (lean_obj_tag(v_a_2024_) == 5)
{
lean_object* v_val_2028_; uint8_t v_isRec_2029_; 
v_val_2028_ = lean_ctor_get(v_a_2024_, 0);
lean_inc_ref(v_val_2028_);
lean_dec_ref_known(v_a_2024_, 1);
v_isRec_2029_ = lean_ctor_get_uint8(v_val_2028_, sizeof(void*)*6);
if (v_isRec_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec_ref(v_val_2028_);
lean_dec(v_indName_1822_);
v___x_2030_ = lean_box(0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
else
{
lean_object* v_toConstantVal_2034_; lean_object* v_numParams_2035_; lean_object* v_all_2036_; lean_object* v_numNested_2037_; lean_object* v_type_2038_; lean_object* v___x_2039_; 
lean_del_object(v___x_2026_);
v_toConstantVal_2034_ = lean_ctor_get(v_val_2028_, 0);
lean_inc_ref(v_toConstantVal_2034_);
v_numParams_2035_ = lean_ctor_get(v_val_2028_, 1);
lean_inc(v_numParams_2035_);
v_all_2036_ = lean_ctor_get(v_val_2028_, 3);
lean_inc(v_all_2036_);
v_numNested_2037_ = lean_ctor_get(v_val_2028_, 5);
lean_inc(v_numNested_2037_);
lean_dec_ref(v_val_2028_);
v_type_2038_ = lean_ctor_get(v_toConstantVal_2034_, 2);
lean_inc_ref(v_type_2038_);
lean_dec_ref(v_toConstantVal_2034_);
v___x_2039_ = l_Lean_Meta_isPropFormerType(v_type_2038_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2074_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2074_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2074_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_del_object(v___x_2042_);
lean_inc_n(v_indName_1822_, 2);
v___x_2045_ = l_Lean_mkRecName(v_indName_1822_);
v___x_2046_ = l_Lean_mkBelowName(v_indName_1822_);
lean_inc(v___x_2046_);
lean_inc(v_numParams_2035_);
lean_inc(v___x_2045_);
v___x_2047_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2045_, v_numParams_2035_, v___x_2046_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2068_; 
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; 
v_unused_2069_ = lean_ctor_get(v___x_2047_, 0);
lean_dec(v_unused_2069_);
v___x_2049_ = v___x_2047_;
v_isShared_2050_ = v_isSharedCheck_2068_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v___x_2047_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2068_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = l_List_get_x21Internal___redArg(v___x_1832_, v_all_2036_, v___x_2051_);
lean_dec(v_all_2036_);
v___x_2053_ = lean_name_eq(v___x_2052_, v_indName_1822_);
lean_dec(v_indName_1822_);
lean_dec(v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec(v___x_2046_);
lean_dec(v___x_2045_);
lean_dec(v_numNested_2037_);
lean_dec(v_numParams_2035_);
v___x_2054_ = lean_box(0);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2054_);
v___x_2056_ = v___x_2049_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_del_object(v___x_2049_);
v___x_2058_ = lean_box(0);
v___x_2059_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2037_, v___x_2045_, v___x_2046_, v_numParams_2035_, v___x_2051_, v___x_2058_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_numNested_2037_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; 
v_unused_2067_ = lean_ctor_get(v___x_2059_, 0);
lean_dec(v_unused_2067_);
v___x_2061_ = v___x_2059_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v___x_2059_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2058_);
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2058_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
else
{
return v___x_2059_;
}
}
}
}
else
{
lean_dec(v___x_2046_);
lean_dec(v___x_2045_);
lean_dec(v_numNested_2037_);
lean_dec(v_all_2036_);
lean_dec(v_numParams_2035_);
lean_dec(v_indName_1822_);
return v___x_2047_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
lean_dec(v_numNested_2037_);
lean_dec(v_all_2036_);
lean_dec(v_numParams_2035_);
lean_dec(v_indName_1822_);
v___x_2070_ = lean_box(0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2070_);
v___x_2072_ = v___x_2042_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_numNested_2037_);
lean_dec(v_all_2036_);
lean_dec(v_numParams_2035_);
lean_dec(v_indName_1822_);
v_a_2075_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2039_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2039_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec(v_a_2024_);
lean_dec(v_indName_1822_);
v___x_2083_ = lean_box(0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2083_);
v___x_2085_ = v___x_2026_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_indName_1822_);
v_a_2088_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2023_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2023_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
goto v___jp_1958_;
}
}
else
{
goto v___jp_1958_;
}
v___jp_1911_:
{
lean_object* v___x_1915_; double v___x_1916_; double v___x_1917_; double v___x_1918_; double v___x_1919_; double v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1915_ = lean_io_mono_nanos_now();
v___x_1916_ = lean_float_of_nat(v___y_1913_);
v___x_1917_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1918_ = lean_float_div(v___x_1916_, v___x_1917_);
v___x_1919_ = lean_float_of_nat(v___x_1915_);
v___x_1920_ = lean_float_div(v___x_1919_, v___x_1917_);
v___x_1921_ = lean_box_float(v___x_1918_);
v___x_1922_ = lean_box_float(v___x_1920_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1914_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1907_, v_hasTrace_1831_, v___x_1908_, v_options_1829_, v___x_1910_, v___y_1912_, v___f_1906_, v___x_1924_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
return v___x_1925_;
}
v___jp_1926_:
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1929_);
v___y_1912_ = v___y_1927_;
v___y_1913_ = v___y_1928_;
v_a_1914_ = v___x_1930_;
goto v___jp_1911_;
}
v___jp_1931_:
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1934_);
v___y_1912_ = v___y_1932_;
v___y_1913_ = v___y_1933_;
v_a_1914_ = v___x_1935_;
goto v___jp_1911_;
}
v___jp_1936_:
{
lean_object* v___x_1940_; double v___x_1941_; double v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1940_ = lean_io_get_num_heartbeats();
v___x_1941_ = lean_float_of_nat(v___y_1938_);
v___x_1942_ = lean_float_of_nat(v___x_1940_);
v___x_1943_ = lean_box_float(v___x_1941_);
v___x_1944_ = lean_box_float(v___x_1942_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_a_1939_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1907_, v_hasTrace_1831_, v___x_1908_, v_options_1829_, v___x_1910_, v___y_1937_, v___f_1906_, v___x_1946_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
return v___x_1947_;
}
v___jp_1948_:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1951_);
v___y_1937_ = v___y_1949_;
v___y_1938_ = v___y_1950_;
v_a_1939_ = v___x_1952_;
goto v___jp_1936_;
}
v___jp_1953_:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1957_, 0, v_a_1956_);
v___y_1937_ = v___y_1954_;
v___y_1938_ = v___y_1955_;
v_a_1939_ = v___x_1957_;
goto v___jp_1936_;
}
v___jp_1958_:
{
lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1826_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1962_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1829_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1822_);
v___x_1964_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
if (lean_obj_tag(v_a_1965_) == 5)
{
lean_object* v_val_1966_; uint8_t v_isRec_1967_; 
v_val_1966_ = lean_ctor_get(v_a_1965_, 0);
lean_inc_ref(v_val_1966_);
lean_dec_ref_known(v_a_1965_, 1);
v_isRec_1967_ = lean_ctor_get_uint8(v_val_1966_, sizeof(void*)*6);
if (v_isRec_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_val_1966_);
lean_dec(v_indName_1822_);
v___x_1968_ = lean_box(0);
v___y_1927_ = v_a_1960_;
v___y_1928_ = v___x_1963_;
v_a_1929_ = v___x_1968_;
goto v___jp_1926_;
}
else
{
lean_object* v_toConstantVal_1969_; lean_object* v_numParams_1970_; lean_object* v_all_1971_; lean_object* v_numNested_1972_; lean_object* v_type_1973_; lean_object* v___x_1974_; 
v_toConstantVal_1969_ = lean_ctor_get(v_val_1966_, 0);
lean_inc_ref(v_toConstantVal_1969_);
v_numParams_1970_ = lean_ctor_get(v_val_1966_, 1);
lean_inc(v_numParams_1970_);
v_all_1971_ = lean_ctor_get(v_val_1966_, 3);
lean_inc(v_all_1971_);
v_numNested_1972_ = lean_ctor_get(v_val_1966_, 5);
lean_inc(v_numNested_1972_);
lean_dec_ref(v_val_1966_);
v_type_1973_ = lean_ctor_get(v_toConstantVal_1969_, 2);
lean_inc_ref(v_type_1973_);
lean_dec_ref(v_toConstantVal_1969_);
v___x_1974_ = l_Lean_Meta_isPropFormerType(v_type_1973_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; uint8_t v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_inc_n(v_indName_1822_, 2);
v___x_1977_ = l_Lean_mkRecName(v_indName_1822_);
v___x_1978_ = l_Lean_mkBelowName(v_indName_1822_);
lean_inc(v___x_1978_);
lean_inc(v_numParams_1970_);
lean_inc(v___x_1977_);
v___x_1979_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1977_, v_numParams_1970_, v___x_1978_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
lean_dec_ref_known(v___x_1979_, 1);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = l_List_get_x21Internal___redArg(v___x_1832_, v_all_1971_, v___x_1980_);
lean_dec(v_all_1971_);
v___x_1982_ = lean_name_eq(v___x_1981_, v_indName_1822_);
lean_dec(v_indName_1822_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec(v___x_1978_);
lean_dec(v___x_1977_);
lean_dec(v_numNested_1972_);
lean_dec(v_numParams_1970_);
v___x_1983_ = lean_box(0);
v___y_1927_ = v_a_1960_;
v___y_1928_ = v___x_1963_;
v_a_1929_ = v___x_1983_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1972_, v___x_1977_, v___x_1978_, v_numParams_1970_, v___x_1980_, v___x_1984_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_numNested_1972_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_dec_ref_known(v___x_1985_, 1);
v___y_1927_ = v_a_1960_;
v___y_1928_ = v___x_1963_;
v_a_1929_ = v___x_1984_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___y_1932_ = v_a_1960_;
v___y_1933_ = v___x_1963_;
v_a_1934_ = v_a_1986_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v_a_1987_; 
lean_dec(v___x_1978_);
lean_dec(v___x_1977_);
lean_dec(v_numNested_1972_);
lean_dec(v_all_1971_);
lean_dec(v_numParams_1970_);
lean_dec(v_indName_1822_);
v_a_1987_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1979_, 1);
v___y_1932_ = v_a_1960_;
v___y_1933_ = v___x_1963_;
v_a_1934_ = v_a_1987_;
goto v___jp_1931_;
}
}
else
{
lean_object* v___x_1988_; 
lean_dec(v_numNested_1972_);
lean_dec(v_all_1971_);
lean_dec(v_numParams_1970_);
lean_dec(v_indName_1822_);
v___x_1988_ = lean_box(0);
v___y_1927_ = v_a_1960_;
v___y_1928_ = v___x_1963_;
v_a_1929_ = v___x_1988_;
goto v___jp_1926_;
}
}
else
{
lean_object* v_a_1989_; 
lean_dec(v_numNested_1972_);
lean_dec(v_all_1971_);
lean_dec(v_numParams_1970_);
lean_dec(v_indName_1822_);
v_a_1989_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1974_, 1);
v___y_1932_ = v_a_1960_;
v___y_1933_ = v___x_1963_;
v_a_1934_ = v_a_1989_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v___x_1990_; 
lean_dec(v_a_1965_);
lean_dec(v_indName_1822_);
v___x_1990_ = lean_box(0);
v___y_1927_ = v_a_1960_;
v___y_1928_ = v___x_1963_;
v_a_1929_ = v___x_1990_;
goto v___jp_1926_;
}
}
else
{
lean_object* v_a_1991_; 
lean_dec(v_indName_1822_);
v_a_1991_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1964_, 1);
v___y_1932_ = v_a_1960_;
v___y_1933_ = v___x_1963_;
v_a_1934_ = v_a_1991_;
goto v___jp_1931_;
}
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1822_);
v___x_1993_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_a_1994_) == 5)
{
lean_object* v_val_1995_; uint8_t v_isRec_1996_; 
v_val_1995_ = lean_ctor_get(v_a_1994_, 0);
lean_inc_ref(v_val_1995_);
lean_dec_ref_known(v_a_1994_, 1);
v_isRec_1996_ = lean_ctor_get_uint8(v_val_1995_, sizeof(void*)*6);
if (v_isRec_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v_val_1995_);
lean_dec(v_indName_1822_);
v___x_1997_ = lean_box(0);
v___y_1949_ = v_a_1960_;
v___y_1950_ = v___x_1992_;
v_a_1951_ = v___x_1997_;
goto v___jp_1948_;
}
else
{
lean_object* v_toConstantVal_1998_; lean_object* v_numParams_1999_; lean_object* v_all_2000_; lean_object* v_numNested_2001_; lean_object* v_type_2002_; lean_object* v___x_2003_; 
v_toConstantVal_1998_ = lean_ctor_get(v_val_1995_, 0);
lean_inc_ref(v_toConstantVal_1998_);
v_numParams_1999_ = lean_ctor_get(v_val_1995_, 1);
lean_inc(v_numParams_1999_);
v_all_2000_ = lean_ctor_get(v_val_1995_, 3);
lean_inc(v_all_2000_);
v_numNested_2001_ = lean_ctor_get(v_val_1995_, 5);
lean_inc(v_numNested_2001_);
lean_dec_ref(v_val_1995_);
v_type_2002_ = lean_ctor_get(v_toConstantVal_1998_, 2);
lean_inc_ref(v_type_2002_);
lean_dec_ref(v_toConstantVal_1998_);
v___x_2003_ = l_Lean_Meta_isPropFormerType(v_type_2002_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; uint8_t v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = lean_unbox(v_a_2004_);
lean_dec(v_a_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_inc_n(v_indName_1822_, 2);
v___x_2006_ = l_Lean_mkRecName(v_indName_1822_);
v___x_2007_ = l_Lean_mkBelowName(v_indName_1822_);
lean_inc(v___x_2007_);
lean_inc(v_numParams_1999_);
lean_inc(v___x_2006_);
v___x_2008_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2006_, v_numParams_1999_, v___x_2007_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; uint8_t v___x_2011_; 
lean_dec_ref_known(v___x_2008_, 1);
v___x_2009_ = lean_unsigned_to_nat(0u);
v___x_2010_ = l_List_get_x21Internal___redArg(v___x_1832_, v_all_2000_, v___x_2009_);
lean_dec(v_all_2000_);
v___x_2011_ = lean_name_eq(v___x_2010_, v_indName_1822_);
lean_dec(v_indName_1822_);
lean_dec(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec(v___x_2007_);
lean_dec(v___x_2006_);
lean_dec(v_numNested_2001_);
lean_dec(v_numParams_1999_);
v___x_2012_ = lean_box(0);
v___y_1949_ = v_a_1960_;
v___y_1950_ = v___x_1992_;
v_a_1951_ = v___x_2012_;
goto v___jp_1948_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2001_, v___x_2006_, v___x_2007_, v_numParams_1999_, v___x_2009_, v___x_2013_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_numNested_2001_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_dec_ref_known(v___x_2014_, 1);
v___y_1949_ = v_a_1960_;
v___y_1950_ = v___x_1992_;
v_a_1951_ = v___x_2013_;
goto v___jp_1948_;
}
else
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1954_ = v_a_1960_;
v___y_1955_ = v___x_1992_;
v_a_1956_ = v_a_2015_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v_a_2016_; 
lean_dec(v___x_2007_);
lean_dec(v___x_2006_);
lean_dec(v_numNested_2001_);
lean_dec(v_all_2000_);
lean_dec(v_numParams_1999_);
lean_dec(v_indName_1822_);
v_a_2016_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2008_, 1);
v___y_1954_ = v_a_1960_;
v___y_1955_ = v___x_1992_;
v_a_1956_ = v_a_2016_;
goto v___jp_1953_;
}
}
else
{
lean_object* v___x_2017_; 
lean_dec(v_numNested_2001_);
lean_dec(v_all_2000_);
lean_dec(v_numParams_1999_);
lean_dec(v_indName_1822_);
v___x_2017_ = lean_box(0);
v___y_1949_ = v_a_1960_;
v___y_1950_ = v___x_1992_;
v_a_1951_ = v___x_2017_;
goto v___jp_1948_;
}
}
else
{
lean_object* v_a_2018_; 
lean_dec(v_numNested_2001_);
lean_dec(v_all_2000_);
lean_dec(v_numParams_1999_);
lean_dec(v_indName_1822_);
v_a_2018_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1954_ = v_a_1960_;
v___y_1955_ = v___x_1992_;
v_a_1956_ = v_a_2018_;
goto v___jp_1953_;
}
}
}
else
{
lean_object* v___x_2019_; 
lean_dec(v_a_1994_);
lean_dec(v_indName_1822_);
v___x_2019_ = lean_box(0);
v___y_1949_ = v_a_1960_;
v___y_1950_ = v___x_1992_;
v_a_1951_ = v___x_2019_;
goto v___jp_1948_;
}
}
else
{
lean_object* v_a_2020_; 
lean_dec(v_indName_1822_);
v_a_2020_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_1993_, 1);
v___y_1954_ = v_a_1960_;
v___y_1955_ = v___x_1992_;
v_a_1956_ = v_a_2020_;
goto v___jp_1953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_mkBelow(v_indName_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v___x_2106_, lean_object* v_inst_2107_, lean_object* v_R_2108_, lean_object* v_a_2109_, lean_object* v_b_2110_, lean_object* v_c_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2103_, v___x_2104_, v___x_2105_, v___x_2106_, v_a_2109_, v_b_2110_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v___x_2121_, lean_object* v_inst_2122_, lean_object* v_R_2123_, lean_object* v_a_2124_, lean_object* v_b_2125_, lean_object* v_c_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2118_, v___x_2119_, v___x_2120_, v___x_2121_, v_inst_2122_, v_R_2123_, v_a_2124_, v_b_2125_, v_c_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v_upperBound_2118_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2133_, lean_object* v_x_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2134_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2141_, lean_object* v_x_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2141_, v_x_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
if (lean_obj_tag(v_a_2149_) == 0)
{
lean_object* v___x_2151_; 
v___x_2151_ = l_List_reverse___redArg(v_a_2150_);
return v___x_2151_;
}
else
{
lean_object* v_head_2152_; lean_object* v_tail_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2162_; 
v_head_2152_ = lean_ctor_get(v_a_2149_, 0);
v_tail_2153_ = lean_ctor_get(v_a_2149_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_a_2149_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2155_ = v_a_2149_;
v_isShared_2156_ = v_isSharedCheck_2162_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_tail_2153_);
lean_inc(v_head_2152_);
lean_dec(v_a_2149_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2162_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = l_Lean_MessageData_ofExpr(v_head_2152_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 1, v_a_2150_);
lean_ctor_set(v___x_2155_, 0, v___x_2157_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_a_2150_);
v___x_2159_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
v_a_2149_ = v_tail_2153_;
v_a_2150_ = v___x_2159_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2163_, lean_object* v_v_2164_, lean_object* v_i_2165_){
_start:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_array_get_size(v_xs_2163_);
v___x_2167_ = lean_nat_dec_lt(v_i_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v_i_2165_);
v___x_2168_ = lean_box(0);
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = lean_array_fget_borrowed(v_xs_2163_, v_i_2165_);
v___x_2170_ = lean_expr_eqv(v___x_2169_, v_v_2164_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_i_2165_, v___x_2171_);
lean_dec(v_i_2165_);
v_i_2165_ = v___x_2172_;
goto _start;
}
else
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_i_2165_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2175_, lean_object* v_v_2176_, lean_object* v_i_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2175_, v_v_2176_, v_i_2177_);
lean_dec_ref(v_v_2176_);
lean_dec_ref(v_xs_2175_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2179_, lean_object* v_v_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_unsigned_to_nat(0u);
v___x_2182_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2179_, v_v_2180_, v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2183_, lean_object* v_v_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2183_, v_v_2184_);
lean_dec_ref(v_v_2184_);
lean_dec_ref(v_xs_2183_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2186_, lean_object* v_v_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2186_, v_v_2187_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_box(0);
return v___x_2189_;
}
else
{
lean_object* v_val_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_val_2190_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2188_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_val_2190_);
lean_dec(v___x_2188_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_val_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2198_, lean_object* v_v_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2198_, v_v_2199_);
lean_dec_ref(v_v_2199_);
lean_dec_ref(v_xs_2198_);
return v_res_2200_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2203_ = l_Lean_stringToMessageData(v___x_2202_);
return v___x_2203_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2207_, lean_object* v_prods_2208_, lean_object* v_motives_2209_, lean_object* v_fs_2210_, lean_object* v_minor__type_2211_, lean_object* v_x_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
if (lean_obj_tag(v_x_2212_) == 5)
{
lean_object* v_fn_2220_; lean_object* v_arg_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_fn_2220_ = lean_ctor_get(v_x_2212_, 0);
lean_inc_ref(v_fn_2220_);
v_arg_2221_ = lean_ctor_get(v_x_2212_, 1);
lean_inc_ref(v_arg_2221_);
lean_dec_ref_known(v_x_2212_, 2);
v___x_2222_ = lean_array_set(v_x_2213_, v_x_2214_, v_arg_2221_);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_nat_sub(v_x_2214_, v___x_2223_);
lean_dec(v_x_2214_);
v_x_2212_ = v_fn_2220_;
v_x_2213_ = v___x_2222_;
v_x_2214_ = v___x_2224_;
goto _start;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v_x_2214_);
v___x_2226_ = l_Lean_instInhabitedExpr;
v___x_2227_ = l_Lean_Meta_PProdN_mk(v_rlvl_2207_, v_prods_2208_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2209_, v_x_2212_);
lean_dec_ref(v_x_2212_);
if (lean_obj_tag(v___x_2229_) == 1)
{
lean_object* v_val_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec_ref(v_minor__type_2211_);
lean_dec_ref(v_motives_2209_);
v_val_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v___x_2229_, 1);
v___x_2231_ = lean_array_get_borrowed(v___x_2226_, v_fs_2210_, v_val_2230_);
lean_dec(v_val_2230_);
lean_inc(v_a_2228_);
v___x_2232_ = lean_array_push(v_x_2213_, v_a_2228_);
lean_inc(v___x_2231_);
v___x_2233_ = l_Lean_mkAppN(v___x_2231_, v___x_2232_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = l_Lean_Meta_mkPProdMk(v___x_2233_, v_a_2228_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v___x_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_x_2213_);
v___x_2235_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2236_ = l_Lean_MessageData_ofExpr(v_minor__type_2211_);
v___x_2237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_array_to_list(v_motives_2209_);
v___x_2241_ = lean_box(0);
v___x_2242_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2240_, v___x_2241_);
v___x_2243_ = l_Lean_MessageData_ofList(v___x_2242_);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2239_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2244_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2245_;
}
}
else
{
lean_dec_ref(v_x_2213_);
lean_dec_ref(v_x_2212_);
lean_dec_ref(v_minor__type_2211_);
lean_dec_ref(v_motives_2209_);
return v___x_2227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2246_, lean_object* v_prods_2247_, lean_object* v_motives_2248_, lean_object* v_fs_2249_, lean_object* v_minor__type_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2246_, v_prods_2247_, v_motives_2248_, v_fs_2249_, v_minor__type_2250_, v_x_2251_, v_x_2252_, v_x_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_fs_2249_);
return v_res_2259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2260_; lean_object* v_dummy_2261_; 
v___x_2260_ = lean_box(0);
v_dummy_2261_ = l_Lean_Expr_sort___override(v___x_2260_);
return v_dummy_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2262_, lean_object* v_head_2263_, lean_object* v_belows_2264_, lean_object* v_prods_2265_, lean_object* v_rlvl_2266_, lean_object* v_fs_2267_, lean_object* v_minor__type_2268_, lean_object* v_tail_2269_, lean_object* v_arg__args_2270_, lean_object* v_arg__type_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2262_, v_head_2263_, v_belows_2264_, v_prods_2265_, v_rlvl_2266_, v_fs_2267_, v_minor__type_2268_, v_tail_2269_, v_arg__args_2270_, v_arg__type_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_arg__args_2270_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2278_, lean_object* v_motives_2279_, lean_object* v_belows_2280_, lean_object* v_fs_2281_, lean_object* v_minor__type_2282_, lean_object* v_prods_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
if (lean_obj_tag(v_a_2284_) == 0)
{
lean_object* v_dummy_2290_; lean_object* v_nargs_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v_belows_2280_);
v_dummy_2290_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2291_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2282_);
lean_inc(v_nargs_2291_);
v___x_2292_ = lean_mk_array(v_nargs_2291_, v_dummy_2290_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_sub(v_nargs_2291_, v___x_2293_);
lean_dec(v_nargs_2291_);
lean_inc_ref(v_minor__type_2282_);
v___x_2295_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2278_, v_prods_2283_, v_motives_2279_, v_fs_2281_, v_minor__type_2282_, v_minor__type_2282_, v___x_2292_, v___x_2294_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec_ref(v_fs_2281_);
return v___x_2295_;
}
else
{
lean_object* v_head_2296_; lean_object* v_tail_2297_; lean_object* v___f_2298_; lean_object* v___x_2299_; 
v_head_2296_ = lean_ctor_get(v_a_2284_, 0);
lean_inc_n(v_head_2296_, 2);
v_tail_2297_ = lean_ctor_get(v_a_2284_, 1);
lean_inc(v_tail_2297_);
lean_dec_ref_known(v_a_2284_, 2);
v___f_2298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2298_, 0, v_motives_2279_);
lean_closure_set(v___f_2298_, 1, v_head_2296_);
lean_closure_set(v___f_2298_, 2, v_belows_2280_);
lean_closure_set(v___f_2298_, 3, v_prods_2283_);
lean_closure_set(v___f_2298_, 4, v_rlvl_2278_);
lean_closure_set(v___f_2298_, 5, v_fs_2281_);
lean_closure_set(v___f_2298_, 6, v_minor__type_2282_);
lean_closure_set(v___f_2298_, 7, v_tail_2297_);
lean_inc(v_a_2288_);
lean_inc_ref(v_a_2287_);
lean_inc(v_a_2286_);
lean_inc_ref(v_a_2285_);
v___x_2299_ = lean_infer_type(v_head_2296_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = 0;
v___x_2302_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2300_, v___f_2298_, v___x_2301_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
return v___x_2302_;
}
else
{
lean_dec_ref(v___f_2298_);
return v___x_2299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2303_, lean_object* v_rlvl_2304_, lean_object* v_motives_2305_, lean_object* v_belows_2306_, lean_object* v_fs_2307_, lean_object* v_minor__type_2308_, lean_object* v_tail_2309_, uint8_t v___x_2310_, uint8_t v___x_2311_, uint8_t v___x_2312_, lean_object* v_arg_x27_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_inc_ref(v_arg_x27_2313_);
v___x_2319_ = lean_array_push(v_prods_2303_, v_arg_x27_2313_);
v___x_2320_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2304_, v_motives_2305_, v_belows_2306_, v_fs_2307_, v_minor__type_2308_, v___x_2319_, v_tail_2309_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2324_ = lean_array_push(v___x_2323_, v_arg_x27_2313_);
v___x_2325_ = l_Lean_Meta_mkLambdaFVars(v___x_2324_, v_a_2321_, v___x_2310_, v___x_2311_, v___x_2310_, v___x_2311_, v___x_2312_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec_ref(v___x_2324_);
return v___x_2325_;
}
else
{
lean_dec_ref(v_arg_x27_2313_);
return v___x_2320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2326_, lean_object* v_rlvl_2327_, lean_object* v_motives_2328_, lean_object* v_belows_2329_, lean_object* v_fs_2330_, lean_object* v_minor__type_2331_, lean_object* v_tail_2332_, lean_object* v___x_2333_, lean_object* v___x_2334_, lean_object* v___x_2335_, lean_object* v_arg_x27_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v___x_1689__boxed_2342_; uint8_t v___x_1690__boxed_2343_; uint8_t v___x_1691__boxed_2344_; lean_object* v_res_2345_; 
v___x_1689__boxed_2342_ = lean_unbox(v___x_2333_);
v___x_1690__boxed_2343_ = lean_unbox(v___x_2334_);
v___x_1691__boxed_2344_ = lean_unbox(v___x_2335_);
v_res_2345_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2326_, v_rlvl_2327_, v_motives_2328_, v_belows_2329_, v_fs_2330_, v_minor__type_2331_, v_tail_2332_, v___x_1689__boxed_2342_, v___x_1690__boxed_2343_, v___x_1691__boxed_2344_, v_arg_x27_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2346_, lean_object* v_head_2347_, lean_object* v_belows_2348_, lean_object* v_arg__type_2349_, lean_object* v_prods_2350_, lean_object* v_rlvl_2351_, lean_object* v_fs_2352_, lean_object* v_minor__type_2353_, lean_object* v_tail_2354_, lean_object* v_arg__args_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 5)
{
lean_object* v_fn_2364_; lean_object* v_arg_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_fn_2364_ = lean_ctor_get(v_x_2356_, 0);
lean_inc_ref(v_fn_2364_);
v_arg_2365_ = lean_ctor_get(v_x_2356_, 1);
lean_inc_ref(v_arg_2365_);
lean_dec_ref_known(v_x_2356_, 2);
v___x_2366_ = lean_array_set(v_x_2357_, v_x_2358_, v_arg_2365_);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_sub(v_x_2358_, v___x_2367_);
lean_dec(v_x_2358_);
v_x_2356_ = v_fn_2364_;
v_x_2357_ = v___x_2366_;
v_x_2358_ = v___x_2368_;
goto _start;
}
else
{
lean_object* v___x_2370_; 
lean_dec(v_x_2358_);
v___x_2370_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2346_, v_x_2356_);
lean_dec_ref(v_x_2356_);
if (lean_obj_tag(v___x_2370_) == 1)
{
lean_object* v_val_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_val_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_val_2371_);
lean_dec_ref_known(v___x_2370_, 1);
v___x_2372_ = l_Lean_instInhabitedExpr;
v___x_2373_ = l_Lean_Expr_fvarId_x21(v_head_2347_);
lean_dec_ref(v_head_2347_);
v___x_2374_ = l_Lean_FVarId_getUserName___redArg(v___x_2373_, v___y_2359_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = lean_array_get_borrowed(v___x_2372_, v_belows_2348_, v_val_2371_);
lean_dec(v_val_2371_);
lean_inc(v___x_2376_);
v___x_2377_ = l_Lean_mkAppN(v___x_2376_, v_x_2357_);
lean_dec_ref(v_x_2357_);
v___x_2378_ = l_Lean_Meta_mkPProd(v_arg__type_2349_, v___x_2377_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; uint8_t v___x_2380_; uint8_t v___x_2381_; uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___f_2386_; lean_object* v___x_2387_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = 0;
v___x_2381_ = 1;
v___x_2382_ = 1;
v___x_2383_ = lean_box(v___x_2380_);
v___x_2384_ = lean_box(v___x_2381_);
v___x_2385_ = lean_box(v___x_2382_);
v___f_2386_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2386_, 0, v_prods_2350_);
lean_closure_set(v___f_2386_, 1, v_rlvl_2351_);
lean_closure_set(v___f_2386_, 2, v_motives_2346_);
lean_closure_set(v___f_2386_, 3, v_belows_2348_);
lean_closure_set(v___f_2386_, 4, v_fs_2352_);
lean_closure_set(v___f_2386_, 5, v_minor__type_2353_);
lean_closure_set(v___f_2386_, 6, v_tail_2354_);
lean_closure_set(v___f_2386_, 7, v___x_2383_);
lean_closure_set(v___f_2386_, 8, v___x_2384_);
lean_closure_set(v___f_2386_, 9, v___x_2385_);
v___x_2387_ = l_Lean_Meta_mkForallFVars(v_arg__args_2355_, v_a_2379_, v___x_2380_, v___x_2381_, v___x_2381_, v___x_2382_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2389_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2387_, 1);
v___x_2389_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2375_, v_a_2388_, v___f_2386_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2389_;
}
else
{
lean_dec_ref(v___f_2386_);
lean_dec(v_a_2375_);
return v___x_2387_;
}
}
else
{
lean_dec(v_a_2375_);
lean_dec(v_tail_2354_);
lean_dec_ref(v_minor__type_2353_);
lean_dec_ref(v_fs_2352_);
lean_dec(v_rlvl_2351_);
lean_dec_ref(v_prods_2350_);
lean_dec_ref(v_belows_2348_);
lean_dec_ref(v_motives_2346_);
return v___x_2378_;
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_val_2371_);
lean_dec_ref(v_x_2357_);
lean_dec(v_tail_2354_);
lean_dec_ref(v_minor__type_2353_);
lean_dec_ref(v_fs_2352_);
lean_dec(v_rlvl_2351_);
lean_dec_ref(v_prods_2350_);
lean_dec_ref(v_arg__type_2349_);
lean_dec_ref(v_belows_2348_);
lean_dec_ref(v_motives_2346_);
v_a_2390_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2374_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2374_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v___x_2398_; 
lean_dec(v___x_2370_);
lean_dec_ref(v_x_2357_);
lean_dec_ref(v_arg__type_2349_);
v___x_2398_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2351_, v_motives_2346_, v_belows_2348_, v_fs_2352_, v_minor__type_2353_, v_prods_2350_, v_tail_2354_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; uint8_t v___x_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_mk_empty_array_with_capacity(v___x_2400_);
v___x_2402_ = lean_array_push(v___x_2401_, v_head_2347_);
v___x_2403_ = 0;
v___x_2404_ = 1;
v___x_2405_ = 1;
v___x_2406_ = l_Lean_Meta_mkLambdaFVars(v___x_2402_, v_a_2399_, v___x_2403_, v___x_2404_, v___x_2403_, v___x_2404_, v___x_2405_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec_ref(v___x_2402_);
return v___x_2406_;
}
else
{
lean_dec_ref(v_head_2347_);
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2407_, lean_object* v_head_2408_, lean_object* v_belows_2409_, lean_object* v_prods_2410_, lean_object* v_rlvl_2411_, lean_object* v_fs_2412_, lean_object* v_minor__type_2413_, lean_object* v_tail_2414_, lean_object* v_arg__args_2415_, lean_object* v_arg__type_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_dummy_2422_; lean_object* v_nargs_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_dummy_2422_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2423_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2416_);
lean_inc(v_nargs_2423_);
v___x_2424_ = lean_mk_array(v_nargs_2423_, v_dummy_2422_);
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_sub(v_nargs_2423_, v___x_2425_);
lean_dec(v_nargs_2423_);
lean_inc_ref(v_arg__type_2416_);
v___x_2427_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2407_, v_head_2408_, v_belows_2409_, v_arg__type_2416_, v_prods_2410_, v_rlvl_2411_, v_fs_2412_, v_minor__type_2413_, v_tail_2414_, v_arg__args_2415_, v_arg__type_2416_, v___x_2424_, v___x_2426_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2428_, lean_object* v_motives_2429_, lean_object* v_belows_2430_, lean_object* v_fs_2431_, lean_object* v_minor__type_2432_, lean_object* v_prods_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2428_, v_motives_2429_, v_belows_2430_, v_fs_2431_, v_minor__type_2432_, v_prods_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2441_ = _args[0];
lean_object* v_head_2442_ = _args[1];
lean_object* v_belows_2443_ = _args[2];
lean_object* v_arg__type_2444_ = _args[3];
lean_object* v_prods_2445_ = _args[4];
lean_object* v_rlvl_2446_ = _args[5];
lean_object* v_fs_2447_ = _args[6];
lean_object* v_minor__type_2448_ = _args[7];
lean_object* v_tail_2449_ = _args[8];
lean_object* v_arg__args_2450_ = _args[9];
lean_object* v_x_2451_ = _args[10];
lean_object* v_x_2452_ = _args[11];
lean_object* v_x_2453_ = _args[12];
lean_object* v___y_2454_ = _args[13];
lean_object* v___y_2455_ = _args[14];
lean_object* v___y_2456_ = _args[15];
lean_object* v___y_2457_ = _args[16];
lean_object* v___y_2458_ = _args[17];
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2441_, v_head_2442_, v_belows_2443_, v_arg__type_2444_, v_prods_2445_, v_rlvl_2446_, v_fs_2447_, v_minor__type_2448_, v_tail_2449_, v_arg__args_2450_, v_x_2451_, v_x_2452_, v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec_ref(v_arg__args_2450_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2460_, lean_object* v_motives_2461_, lean_object* v_belows_2462_, lean_object* v_fs_2463_, lean_object* v_minor__args_2464_, lean_object* v_minor__type_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2472_ = lean_array_to_list(v_minor__args_2464_);
v___x_2473_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2460_, v_motives_2461_, v_belows_2462_, v_fs_2463_, v_minor__type_2465_, v___x_2471_, v___x_2472_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2474_, lean_object* v_motives_2475_, lean_object* v_belows_2476_, lean_object* v_fs_2477_, lean_object* v_minor__args_2478_, lean_object* v_minor__type_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2474_, v_motives_2475_, v_belows_2476_, v_fs_2477_, v_minor__args_2478_, v_minor__type_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2486_, lean_object* v_motives_2487_, lean_object* v_belows_2488_, lean_object* v_fs_2489_, lean_object* v_minorType_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___f_2496_; uint8_t v___x_2497_; lean_object* v___x_2498_; 
v___f_2496_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2496_, 0, v_rlvl_2486_);
lean_closure_set(v___f_2496_, 1, v_motives_2487_);
lean_closure_set(v___f_2496_, 2, v_belows_2488_);
lean_closure_set(v___f_2496_, 3, v_fs_2489_);
v___x_2497_ = 0;
v___x_2498_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2490_, v___f_2496_, v___x_2497_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2499_, lean_object* v_motives_2500_, lean_object* v_belows_2501_, lean_object* v_fs_2502_, lean_object* v_minorType_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2499_, v_motives_2500_, v_belows_2501_, v_fs_2502_, v_minorType_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___f_2516_; lean_object* v___x_28156__overap_2517_; lean_object* v___x_2518_; 
v___f_2516_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_28156__overap_2517_ = lean_panic_fn_borrowed(v___f_2516_, v_msg_2510_);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
v___x_2518_ = lean_apply_5(v___x_28156__overap_2517_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, lean_box(0));
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = l_Lean_Expr_hasMVar(v_e_2526_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_e_2526_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v_mctx_2532_; lean_object* v___x_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; lean_object* v_cache_2537_; lean_object* v_zetaDeltaFVarIds_2538_; lean_object* v_postponed_2539_; lean_object* v_diag_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2549_; 
v___x_2531_ = lean_st_ref_get(v___y_2527_);
v_mctx_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc_ref(v_mctx_2532_);
lean_dec(v___x_2531_);
v___x_2533_ = l_Lean_instantiateMVarsCore(v_mctx_2532_, v_e_2526_);
v_fst_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_snd_2535_);
lean_dec_ref(v___x_2533_);
v___x_2536_ = lean_st_ref_take(v___y_2527_);
v_cache_2537_ = lean_ctor_get(v___x_2536_, 1);
v_zetaDeltaFVarIds_2538_ = lean_ctor_get(v___x_2536_, 2);
v_postponed_2539_ = lean_ctor_get(v___x_2536_, 3);
v_diag_2540_ = lean_ctor_get(v___x_2536_, 4);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2550_);
v___x_2542_ = v___x_2536_;
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_diag_2540_);
lean_inc(v_postponed_2539_);
lean_inc(v_zetaDeltaFVarIds_2538_);
lean_inc(v_cache_2537_);
lean_dec(v___x_2536_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2549_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v_snd_2535_);
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_snd_2535_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_cache_2537_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v_zetaDeltaFVarIds_2538_);
lean_ctor_set(v_reuseFailAlloc_2548_, 3, v_postponed_2539_);
lean_ctor_set(v_reuseFailAlloc_2548_, 4, v_diag_2540_);
v___x_2545_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_st_ref_put(v___y_2527_, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_fst_2534_);
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2551_, v___y_2552_);
lean_dec(v___y_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2555_, v___y_2557_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v_env_2573_; lean_object* v_toConstantVal_2574_; lean_object* v_value_2575_; lean_object* v_all_2576_; lean_object* v_type_2583_; uint8_t v___x_2584_; 
v___x_2572_ = lean_st_ref_get(v___y_2570_);
v_env_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc_ref_n(v_env_2573_, 2);
lean_dec(v___x_2572_);
v_toConstantVal_2574_ = lean_ctor_get(v_thm_2569_, 0);
v_value_2575_ = lean_ctor_get(v_thm_2569_, 1);
v_all_2576_ = lean_ctor_get(v_thm_2569_, 2);
v_type_2583_ = lean_ctor_get(v_toConstantVal_2574_, 2);
v___x_2584_ = l_Lean_Environment_hasUnsafe(v_env_2573_, v_type_2583_);
if (v___x_2584_ == 0)
{
uint8_t v___x_2585_; 
v___x_2585_ = l_Lean_Environment_hasUnsafe(v_env_2573_, v_value_2575_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_thm_2569_);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
else
{
lean_inc(v_all_2576_);
lean_inc_ref(v_value_2575_);
lean_inc_ref(v_toConstantVal_2574_);
lean_dec_ref(v_thm_2569_);
goto v___jp_2577_;
}
}
else
{
lean_inc(v_all_2576_);
lean_inc_ref(v_value_2575_);
lean_inc_ref(v_toConstantVal_2574_);
lean_dec_ref(v_env_2573_);
lean_dec_ref(v_thm_2569_);
goto v___jp_2577_;
}
v___jp_2577_:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2578_ = lean_box(0);
v___x_2579_ = 0;
v___x_2580_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2580_, 0, v_toConstantVal_2574_);
lean_ctor_set(v___x_2580_, 1, v_value_2575_);
lean_ctor_set(v___x_2580_, 2, v___x_2578_);
lean_ctor_set(v___x_2580_, 3, v_all_2576_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*4, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2588_, v___y_2589_);
lean_dec(v___y_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2592_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v_all_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v___x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v___y_2616_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2620_ = lean_array_get_size(v_all_2610_);
v___x_2621_ = lean_nat_dec_lt(v_x_2614_, v___x_2620_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2622_ = lean_array_get_borrowed(v___x_2611_, v_all_2610_, v___x_2612_);
v___x_2623_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2624_ = lean_nat_sub(v_x_2614_, v___x_2620_);
v___x_2625_ = lean_nat_add(v___x_2624_, v___x_2613_);
lean_dec(v___x_2624_);
v___x_2626_ = l_Nat_reprFast(v___x_2625_);
v___x_2627_ = lean_string_append(v___x_2623_, v___x_2626_);
lean_dec_ref(v___x_2626_);
lean_inc(v___x_2622_);
v___x_2628_ = l_Lean_Name_str___override(v___x_2622_, v___x_2627_);
v___y_2616_ = v___x_2628_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_array_fget_borrowed(v_all_2610_, v_x_2614_);
lean_inc(v___x_2629_);
v___x_2630_ = l_Lean_mkBelowName(v___x_2629_);
v___y_2616_ = v___x_2630_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = l_Lean_Expr_const___override(v___y_2616_, v___x_2607_);
v___x_2618_ = l_Array_append___redArg(v___x_2608_, v___x_2609_);
v___x_2619_ = l_Lean_mkAppN(v___x_2617_, v___x_2618_);
lean_dec_ref(v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v_all_2634_, lean_object* v___x_2635_, lean_object* v___x_2636_, lean_object* v___x_2637_, lean_object* v_x_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2631_, v___x_2632_, v___x_2633_, v_all_2634_, v___x_2635_, v___x_2636_, v___x_2637_, v_x_2638_);
lean_dec(v_x_2638_);
lean_dec(v___x_2637_);
lean_dec(v___x_2636_);
lean_dec(v___x_2635_);
lean_dec_ref(v_all_2634_);
lean_dec_ref(v___x_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v_fs_2643_, lean_object* v_as_2644_, size_t v_sz_2645_, size_t v_i_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
uint8_t v___x_2653_; 
v___x_2653_ = lean_usize_dec_lt(v_i_2646_, v_sz_2645_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v_fs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v___x_2641_);
lean_dec(v___x_2640_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_b_2647_);
return v___x_2654_;
}
else
{
lean_object* v_a_2655_; lean_object* v___x_2656_; 
v_a_2655_ = lean_array_uget_borrowed(v_as_2644_, v_i_2646_);
lean_inc(v___y_2651_);
lean_inc_ref(v___y_2650_);
lean_inc(v___y_2649_);
lean_inc_ref(v___y_2648_);
lean_inc(v_a_2655_);
v___x_2656_ = lean_infer_type(v_a_2655_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
lean_inc_ref(v_fs_2643_);
lean_inc_ref(v___x_2642_);
lean_inc_ref(v___x_2641_);
lean_inc(v___x_2640_);
v___x_2658_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2640_, v___x_2641_, v___x_2642_, v_fs_2643_, v_a_2657_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; size_t v___x_2661_; size_t v___x_2662_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_Expr_app___override(v_b_2647_, v_a_2659_);
v___x_2661_ = ((size_t)1ULL);
v___x_2662_ = lean_usize_add(v_i_2646_, v___x_2661_);
v_i_2646_ = v___x_2662_;
v_b_2647_ = v___x_2660_;
goto _start;
}
else
{
lean_dec_ref(v_b_2647_);
lean_dec_ref(v_fs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v___x_2641_);
lean_dec(v___x_2640_);
return v___x_2658_;
}
}
else
{
lean_dec_ref(v_b_2647_);
lean_dec_ref(v_fs_2643_);
lean_dec_ref(v___x_2642_);
lean_dec_ref(v___x_2641_);
lean_dec(v___x_2640_);
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2664_, lean_object* v___x_2665_, lean_object* v___x_2666_, lean_object* v_fs_2667_, lean_object* v_as_2668_, lean_object* v_sz_2669_, lean_object* v_i_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
size_t v_sz_boxed_2677_; size_t v_i_boxed_2678_; lean_object* v_res_2679_; 
v_sz_boxed_2677_ = lean_unbox_usize(v_sz_2669_);
lean_dec(v_sz_2669_);
v_i_boxed_2678_ = lean_unbox_usize(v_i_2670_);
lean_dec(v_i_2670_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2664_, v___x_2665_, v___x_2666_, v_fs_2667_, v_as_2668_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec_ref(v_as_2668_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2680_, lean_object* v___x_2681_, uint8_t v___x_2682_, lean_object* v_targs_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = l_Lean_mkAppN(v_a_2680_, v_targs_2683_);
v___x_2691_ = l_Lean_mkAppN(v___x_2681_, v_targs_2683_);
v___x_2692_ = l_Lean_Meta_mkPProd(v___x_2690_, v___x_2691_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; uint8_t v___x_2694_; uint8_t v___x_2695_; lean_object* v___x_2696_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = 0;
v___x_2695_ = 1;
v___x_2696_ = l_Lean_Meta_mkLambdaFVars(v_targs_2683_, v_a_2693_, v___x_2694_, v___x_2682_, v___x_2694_, v___x_2682_, v___x_2695_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
return v___x_2696_;
}
else
{
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2697_, lean_object* v___x_2698_, lean_object* v___x_2699_, lean_object* v_targs_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v___x_31431__boxed_2707_; lean_object* v_res_2708_; 
v___x_31431__boxed_2707_ = lean_unbox(v___x_2699_);
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2697_, v___x_2698_, v___x_31431__boxed_2707_, v_targs_2700_, v_x_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v_x_2701_);
lean_dec_ref(v_targs_2700_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2709_, lean_object* v___x_2710_, lean_object* v_as_2711_, size_t v_sz_2712_, size_t v_i_2713_, lean_object* v_b_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = lean_usize_dec_lt(v_i_2713_, v_sz_2712_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_b_2714_);
return v___x_2721_;
}
else
{
lean_object* v_snd_2722_; lean_object* v_fst_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2780_; 
v_snd_2722_ = lean_ctor_get(v_b_2714_, 1);
v_fst_2723_ = lean_ctor_get(v_b_2714_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_b_2714_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2725_ = v_b_2714_;
v_isShared_2726_ = v_isSharedCheck_2780_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_snd_2722_);
lean_inc(v_fst_2723_);
lean_dec(v_b_2714_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2780_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v_array_2727_; lean_object* v_start_2728_; lean_object* v_stop_2729_; uint8_t v___x_2730_; 
v_array_2727_ = lean_ctor_get(v_snd_2722_, 0);
v_start_2728_ = lean_ctor_get(v_snd_2722_, 1);
v_stop_2729_ = lean_ctor_get(v_snd_2722_, 2);
v___x_2730_ = lean_nat_dec_lt(v_start_2728_, v_stop_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2732_; 
if (v_isShared_2726_ == 0)
{
v___x_2732_ = v___x_2725_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2723_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_snd_2722_);
v___x_2732_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
return v___x_2733_;
}
}
else
{
lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2776_; 
lean_inc(v_stop_2729_);
lean_inc(v_start_2728_);
lean_inc_ref(v_array_2727_);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_snd_2722_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; lean_object* v_unused_2779_; 
v_unused_2777_ = lean_ctor_get(v_snd_2722_, 2);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_snd_2722_, 1);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_snd_2722_, 0);
lean_dec(v_unused_2779_);
v___x_2736_ = v_snd_2722_;
v_isShared_2737_ = v_isSharedCheck_2776_;
goto v_resetjp_2735_;
}
else
{
lean_dec(v_snd_2722_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2776_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint8_t v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___f_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2738_ = lean_nat_dec_lt(v___x_2709_, v___x_2710_);
v_a_2739_ = lean_array_uget_borrowed(v_as_2711_, v_i_2713_);
v___x_2740_ = lean_array_fget_borrowed(v_array_2727_, v_start_2728_);
v___x_2741_ = lean_box(v___x_2738_);
lean_inc(v___x_2740_);
lean_inc(v_a_2739_);
v___f_2742_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2742_, 0, v_a_2739_);
lean_closure_set(v___f_2742_, 1, v___x_2740_);
lean_closure_set(v___f_2742_, 2, v___x_2741_);
v___x_2743_ = lean_unsigned_to_nat(1u);
v___x_2744_ = lean_nat_add(v_start_2728_, v___x_2743_);
lean_dec(v_start_2728_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v___x_2744_);
v___x_2746_ = v___x_2736_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_array_2727_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_stop_2729_);
v___x_2746_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
lean_inc(v___y_2718_);
lean_inc_ref(v___y_2717_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v_a_2739_);
v___x_2747_ = lean_infer_type(v_a_2739_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = 0;
v___x_2750_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2748_, v___f_2742_, v___x_2749_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_Expr_app___override(v_fst_2723_, v_a_2751_);
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 1, v___x_2746_);
lean_ctor_set(v___x_2725_, 0, v___x_2752_);
v___x_2754_ = v___x_2725_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2746_);
v___x_2754_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
size_t v___x_2755_; size_t v___x_2756_; 
v___x_2755_ = ((size_t)1ULL);
v___x_2756_ = lean_usize_add(v_i_2713_, v___x_2755_);
v_i_2713_ = v___x_2756_;
v_b_2714_ = v___x_2754_;
goto _start;
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec_ref(v___x_2746_);
lean_del_object(v___x_2725_);
lean_dec(v_fst_2723_);
v_a_2759_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2750_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2750_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_dec_ref(v___x_2746_);
lean_dec_ref(v___f_2742_);
lean_del_object(v___x_2725_);
lean_dec(v_fst_2723_);
v_a_2767_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2747_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2747_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2781_, lean_object* v___x_2782_, lean_object* v_as_2783_, lean_object* v_sz_2784_, lean_object* v_i_2785_, lean_object* v_b_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
size_t v_sz_boxed_2792_; size_t v_i_boxed_2793_; lean_object* v_res_2794_; 
v_sz_boxed_2792_ = lean_unbox_usize(v_sz_2784_);
lean_dec(v_sz_2784_);
v_i_boxed_2793_ = lean_unbox_usize(v_i_2785_);
lean_dec(v_i_2785_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2781_, v___x_2782_, v_as_2783_, v_sz_boxed_2792_, v_i_boxed_2793_, v_b_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec_ref(v_as_2783_);
lean_dec(v___x_2782_);
lean_dec(v___x_2781_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2795_, size_t v_sz_2796_, size_t v_i_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v___x_2804_; 
v___x_2804_ = lean_usize_dec_lt(v_i_2797_, v_sz_2796_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
v___x_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_b_2798_);
return v___x_2805_;
}
else
{
lean_object* v_a_2806_; lean_object* v_toInductionSubgoal_2807_; lean_object* v_mvarId_2808_; uint8_t v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2806_ = lean_array_uget_borrowed(v_as_2795_, v_i_2797_);
v_toInductionSubgoal_2807_ = lean_ctor_get(v_a_2806_, 0);
v_mvarId_2808_ = lean_ctor_get(v_toInductionSubgoal_2807_, 0);
v___x_2809_ = 0;
v___x_2810_ = lean_box(0);
lean_inc(v_mvarId_2808_);
v___x_2811_ = l_Lean_MVarId_refl(v_mvarId_2808_, v___x_2809_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2811_) == 0)
{
size_t v___x_2812_; size_t v___x_2813_; 
lean_dec_ref_known(v___x_2811_, 1);
v___x_2812_ = ((size_t)1ULL);
v___x_2813_ = lean_usize_add(v_i_2797_, v___x_2812_);
v_i_2797_ = v___x_2813_;
v_b_2798_ = v___x_2810_;
goto _start;
}
else
{
return v___x_2811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2815_, lean_object* v_sz_2816_, lean_object* v_i_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
size_t v_sz_boxed_2824_; size_t v_i_boxed_2825_; lean_object* v_res_2826_; 
v_sz_boxed_2824_ = lean_unbox_usize(v_sz_2816_);
lean_dec(v_sz_2816_);
v_i_boxed_2825_ = lean_unbox_usize(v_i_2817_);
lean_dec(v_i_2817_);
v_res_2826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2815_, v_sz_boxed_2824_, v_i_boxed_2825_, v_b_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec_ref(v_as_2815_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2827_, lean_object* v_tail_2828_, lean_object* v_recName_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v_val_2841_, uint8_t v___x_2842_, lean_object* v_brecOnGoName_2843_, lean_object* v_levelParams_2844_, lean_object* v___x_2845_, lean_object* v_brecOnName_2846_, lean_object* v___x_2847_, lean_object* v_brecOnEqName_2848_, lean_object* v_fs_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; size_t v_sz_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
lean_inc(v___x_2827_);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2827_);
lean_ctor_set(v___x_2855_, 1, v_tail_2828_);
v___x_2856_ = l_Lean_Expr_const___override(v_recName_2829_, v___x_2855_);
v___x_2857_ = l_Lean_mkAppN(v___x_2856_, v___x_2830_);
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2831_);
v_sz_2859_ = lean_array_size(v___x_2832_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2833_, v___x_2834_, v___x_2832_, v_sz_2859_, v___x_2860_, v___x_2858_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v_fst_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_3228_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v_fst_2863_ = lean_ctor_get(v_a_2862_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_2862_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_a_2862_, 1);
lean_dec(v_unused_3229_);
v___x_2865_ = v_a_2862_;
v_isShared_2866_ = v_isSharedCheck_3228_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_fst_2863_);
lean_dec(v_a_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_3228_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
size_t v_sz_2867_; lean_object* v___x_2868_; 
v_sz_2867_ = lean_array_size(v___x_2835_);
lean_inc_ref(v_fs_2849_);
lean_inc_ref(v___x_2836_);
lean_inc_ref(v___x_2832_);
v___x_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2827_, v___x_2832_, v___x_2836_, v_fs_2849_, v___x_2835_, v_sz_2867_, v___x_2860_, v_fst_2863_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = l_Lean_mkAppN(v_a_2869_, v___x_2837_);
lean_inc_ref_n(v___x_2838_, 3);
v___x_2871_ = l_Lean_Expr_app___override(v___x_2870_, v___x_2838_);
v___x_2872_ = l_Array_append___redArg(v___x_2830_, v___x_2832_);
v___x_2873_ = l_Array_append___redArg(v___x_2872_, v___x_2837_);
v___x_2874_ = lean_mk_empty_array_with_capacity(v___x_2839_);
v___x_2875_ = lean_array_push(v___x_2874_, v___x_2838_);
v___x_2876_ = l_Array_append___redArg(v___x_2873_, v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_2877_ = l_Array_append___redArg(v___x_2876_, v_fs_2849_);
v___x_2878_ = lean_array_get(v___x_2840_, v___x_2832_, v_val_2841_);
lean_dec_ref(v___x_2832_);
v___x_2879_ = lean_array_push(v___x_2837_, v___x_2838_);
v___x_2880_ = l_Lean_mkAppN(v___x_2878_, v___x_2879_);
v___x_2881_ = lean_array_get(v___x_2840_, v___x_2836_, v_val_2841_);
lean_dec_ref(v___x_2836_);
v___x_2882_ = l_Lean_mkAppN(v___x_2881_, v___x_2879_);
lean_inc_ref(v___x_2880_);
v___x_2883_ = l_Lean_Meta_mkPProd(v___x_2880_, v___x_2882_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; uint8_t v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = 0;
v___x_2886_ = 1;
v___x_2887_ = l_Lean_Meta_mkForallFVars(v___x_2877_, v_a_2884_, v___x_2885_, v___x_2842_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v___x_2889_ = l_Lean_Meta_mkLambdaFVars(v___x_2877_, v___x_2871_, v___x_2885_, v___x_2842_, v___x_2885_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_3195_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = lean_box(1);
lean_inc(v_levelParams_2844_);
lean_inc(v_brecOnGoName_2843_);
v___x_2892_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2843_, v_levelParams_2844_, v_a_2888_, v_a_2890_, v___x_2891_, v___y_2853_);
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_2895_ = v___x_2892_;
v_isShared_2896_ = v_isSharedCheck_3195_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_3195_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
lean_inc(v_a_2893_);
if (v_isShared_2896_ == 0)
{
lean_ctor_set_tag(v___x_2895_, 1);
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_3194_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_addDecl(v___x_2898_, v___x_2885_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_toConstantVal_2900_; lean_object* v_name_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref_known(v___x_2899_, 1);
v_toConstantVal_2900_ = lean_ctor_get(v_a_2893_, 0);
lean_inc_ref(v_toConstantVal_2900_);
lean_dec(v_a_2893_);
v_name_2901_ = lean_ctor_get(v_toConstantVal_2900_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_toConstantVal_2900_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; lean_object* v_unused_3193_; 
v_unused_3192_ = lean_ctor_get(v_toConstantVal_2900_, 2);
lean_dec(v_unused_3192_);
v_unused_3193_ = lean_ctor_get(v_toConstantVal_2900_, 1);
lean_dec(v_unused_3193_);
v___x_2903_ = v_toConstantVal_2900_;
v_isShared_2904_ = v_isSharedCheck_3191_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_name_2901_);
lean_dec(v_toConstantVal_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_3191_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_env_2907_; lean_object* v_nextMacroScope_2908_; lean_object* v_ngen_2909_; lean_object* v_auxDeclNGen_2910_; lean_object* v_traceState_2911_; lean_object* v_recordedDeps_2912_; lean_object* v_messages_2913_; lean_object* v_infoState_2914_; lean_object* v_snapshotTasks_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_3189_; 
lean_inc(v_name_2901_);
v___x_2905_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2901_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec_ref(v___x_2905_);
v___x_2906_ = lean_st_ref_take(v___y_2853_);
v_env_2907_ = lean_ctor_get(v___x_2906_, 0);
v_nextMacroScope_2908_ = lean_ctor_get(v___x_2906_, 1);
v_ngen_2909_ = lean_ctor_get(v___x_2906_, 2);
v_auxDeclNGen_2910_ = lean_ctor_get(v___x_2906_, 3);
v_traceState_2911_ = lean_ctor_get(v___x_2906_, 4);
v_recordedDeps_2912_ = lean_ctor_get(v___x_2906_, 6);
v_messages_2913_ = lean_ctor_get(v___x_2906_, 7);
v_infoState_2914_ = lean_ctor_get(v___x_2906_, 8);
v_snapshotTasks_2915_ = lean_ctor_get(v___x_2906_, 9);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_2906_, 5);
lean_dec(v_unused_3190_);
v___x_2917_ = v___x_2906_;
v_isShared_2918_ = v_isSharedCheck_3189_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_snapshotTasks_2915_);
lean_inc(v_infoState_2914_);
lean_inc(v_messages_2913_);
lean_inc(v_recordedDeps_2912_);
lean_inc(v_traceState_2911_);
lean_inc(v_auxDeclNGen_2910_);
lean_inc(v_ngen_2909_);
lean_inc(v_nextMacroScope_2908_);
lean_inc(v_env_2907_);
lean_dec(v___x_2906_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_3189_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2919_ = l_Lean_addProtected(v_env_2907_, v_name_2901_);
v___x_2920_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 5, v___x_2920_);
lean_ctor_set(v___x_2917_, 0, v___x_2919_);
v___x_2922_ = v___x_2917_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_nextMacroScope_2908_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_ngen_2909_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_auxDeclNGen_2910_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_traceState_2911_);
lean_ctor_set(v_reuseFailAlloc_3188_, 5, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3188_, 6, v_recordedDeps_2912_);
lean_ctor_set(v_reuseFailAlloc_3188_, 7, v_messages_2913_);
lean_ctor_set(v_reuseFailAlloc_3188_, 8, v_infoState_2914_);
lean_ctor_set(v_reuseFailAlloc_3188_, 9, v_snapshotTasks_2915_);
v___x_2922_ = v_reuseFailAlloc_3188_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_mctx_2925_; lean_object* v_zetaDeltaFVarIds_2926_; lean_object* v_postponed_2927_; lean_object* v_diag_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_3186_; 
v___x_2923_ = lean_st_ref_put(v___y_2853_, v___x_2922_);
v___x_2924_ = lean_st_ref_take(v___y_2851_);
v_mctx_2925_ = lean_ctor_get(v___x_2924_, 0);
v_zetaDeltaFVarIds_2926_ = lean_ctor_get(v___x_2924_, 2);
v_postponed_2927_ = lean_ctor_get(v___x_2924_, 3);
v_diag_2928_ = lean_ctor_get(v___x_2924_, 4);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v___x_2924_, 1);
lean_dec(v_unused_3187_);
v___x_2930_ = v___x_2924_;
v_isShared_2931_ = v_isSharedCheck_3186_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_diag_2928_);
lean_inc(v_postponed_2927_);
lean_inc(v_zetaDeltaFVarIds_2926_);
lean_inc(v_mctx_2925_);
lean_dec(v___x_2924_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_3186_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 1, v___x_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_mctx_2925_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_zetaDeltaFVarIds_2926_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_postponed_2927_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_diag_2928_);
v___x_2934_ = v_reuseFailAlloc_3185_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2935_ = lean_st_ref_put(v___y_2851_, v___x_2934_);
lean_inc(v___x_2845_);
v___x_2936_ = l_Lean_Expr_const___override(v_brecOnGoName_2843_, v___x_2845_);
v___x_2937_ = l_Lean_mkAppN(v___x_2936_, v___x_2877_);
lean_inc_ref(v___x_2937_);
v___x_2938_ = l_Lean_Meta_mkPProdFstM(v___x_2937_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l_Lean_Meta_mkLambdaFVars(v___x_2877_, v_a_2939_, v___x_2885_, v___x_2842_, v___x_2885_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v___x_2942_ = l_Lean_Meta_mkForallFVars(v___x_2877_, v___x_2880_, v___x_2885_, v___x_2842_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3160_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
lean_inc(v_levelParams_2844_);
v___x_2944_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2846_, v_levelParams_2844_, v_a_2943_, v_a_2941_, v___x_2891_, v___y_2853_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3160_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3160_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
lean_inc(v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 1);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_3159_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_addDecl(v___x_2950_, v___x_2885_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_toConstantVal_2952_; lean_object* v_name_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref_known(v___x_2951_, 1);
v_toConstantVal_2952_ = lean_ctor_get(v_a_2945_, 0);
lean_inc_ref(v_toConstantVal_2952_);
lean_dec(v_a_2945_);
v_name_2953_ = lean_ctor_get(v_toConstantVal_2952_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v_toConstantVal_2952_);
if (v_isSharedCheck_3156_ == 0)
{
lean_object* v_unused_3157_; lean_object* v_unused_3158_; 
v_unused_3157_ = lean_ctor_get(v_toConstantVal_2952_, 2);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_toConstantVal_2952_, 1);
lean_dec(v_unused_3158_);
v___x_2955_ = v_toConstantVal_2952_;
v_isShared_2956_ = v_isSharedCheck_3156_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_name_2953_);
lean_dec(v_toConstantVal_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3156_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v_env_2959_; lean_object* v_nextMacroScope_2960_; lean_object* v_ngen_2961_; lean_object* v_auxDeclNGen_2962_; lean_object* v_traceState_2963_; lean_object* v_recordedDeps_2964_; lean_object* v_messages_2965_; lean_object* v_infoState_2966_; lean_object* v_snapshotTasks_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3154_; 
lean_inc(v_name_2953_);
v___x_2957_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2953_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec_ref(v___x_2957_);
v___x_2958_ = lean_st_ref_take(v___y_2853_);
v_env_2959_ = lean_ctor_get(v___x_2958_, 0);
v_nextMacroScope_2960_ = lean_ctor_get(v___x_2958_, 1);
v_ngen_2961_ = lean_ctor_get(v___x_2958_, 2);
v_auxDeclNGen_2962_ = lean_ctor_get(v___x_2958_, 3);
v_traceState_2963_ = lean_ctor_get(v___x_2958_, 4);
v_recordedDeps_2964_ = lean_ctor_get(v___x_2958_, 6);
v_messages_2965_ = lean_ctor_get(v___x_2958_, 7);
v_infoState_2966_ = lean_ctor_get(v___x_2958_, 8);
v_snapshotTasks_2967_ = lean_ctor_get(v___x_2958_, 9);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v___x_2958_, 5);
lean_dec(v_unused_3155_);
v___x_2969_ = v___x_2958_;
v_isShared_2970_ = v_isSharedCheck_3154_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_snapshotTasks_2967_);
lean_inc(v_infoState_2966_);
lean_inc(v_messages_2965_);
lean_inc(v_recordedDeps_2964_);
lean_inc(v_traceState_2963_);
lean_inc(v_auxDeclNGen_2962_);
lean_inc(v_ngen_2961_);
lean_inc(v_nextMacroScope_2960_);
lean_inc(v_env_2959_);
lean_dec(v___x_2958_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3154_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_inc(v_name_2953_);
v___x_2971_ = l_Lean_markAuxRecursor(v_env_2959_, v_name_2953_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 5, v___x_2920_);
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v_nextMacroScope_2960_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_ngen_2961_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_auxDeclNGen_2962_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v_traceState_2963_);
lean_ctor_set(v_reuseFailAlloc_3153_, 5, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3153_, 6, v_recordedDeps_2964_);
lean_ctor_set(v_reuseFailAlloc_3153_, 7, v_messages_2965_);
lean_ctor_set(v_reuseFailAlloc_3153_, 8, v_infoState_2966_);
lean_ctor_set(v_reuseFailAlloc_3153_, 9, v_snapshotTasks_2967_);
v___x_2973_ = v_reuseFailAlloc_3153_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_mctx_2976_; lean_object* v_zetaDeltaFVarIds_2977_; lean_object* v_postponed_2978_; lean_object* v_diag_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3151_; 
v___x_2974_ = lean_st_ref_put(v___y_2853_, v___x_2973_);
v___x_2975_ = lean_st_ref_take(v___y_2851_);
v_mctx_2976_ = lean_ctor_get(v___x_2975_, 0);
v_zetaDeltaFVarIds_2977_ = lean_ctor_get(v___x_2975_, 2);
v_postponed_2978_ = lean_ctor_get(v___x_2975_, 3);
v_diag_2979_ = lean_ctor_get(v___x_2975_, 4);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v___x_2975_, 1);
lean_dec(v_unused_3152_);
v___x_2981_ = v___x_2975_;
v_isShared_2982_ = v_isSharedCheck_3151_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_diag_2979_);
lean_inc(v_postponed_2978_);
lean_inc(v_zetaDeltaFVarIds_2977_);
lean_inc(v_mctx_2976_);
lean_dec(v___x_2975_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3151_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_2932_);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_mctx_2976_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_zetaDeltaFVarIds_2977_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_postponed_2978_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_diag_2979_);
v___x_2984_ = v_reuseFailAlloc_3150_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_env_2987_; lean_object* v_nextMacroScope_2988_; lean_object* v_ngen_2989_; lean_object* v_auxDeclNGen_2990_; lean_object* v_traceState_2991_; lean_object* v_recordedDeps_2992_; lean_object* v_messages_2993_; lean_object* v_infoState_2994_; lean_object* v_snapshotTasks_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3148_; 
v___x_2985_ = lean_st_ref_put(v___y_2851_, v___x_2984_);
v___x_2986_ = lean_st_ref_take(v___y_2853_);
v_env_2987_ = lean_ctor_get(v___x_2986_, 0);
v_nextMacroScope_2988_ = lean_ctor_get(v___x_2986_, 1);
v_ngen_2989_ = lean_ctor_get(v___x_2986_, 2);
v_auxDeclNGen_2990_ = lean_ctor_get(v___x_2986_, 3);
v_traceState_2991_ = lean_ctor_get(v___x_2986_, 4);
v_recordedDeps_2992_ = lean_ctor_get(v___x_2986_, 6);
v_messages_2993_ = lean_ctor_get(v___x_2986_, 7);
v_infoState_2994_ = lean_ctor_get(v___x_2986_, 8);
v_snapshotTasks_2995_ = lean_ctor_get(v___x_2986_, 9);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_2986_, 5);
lean_dec(v_unused_3149_);
v___x_2997_ = v___x_2986_;
v_isShared_2998_ = v_isSharedCheck_3148_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_snapshotTasks_2995_);
lean_inc(v_infoState_2994_);
lean_inc(v_messages_2993_);
lean_inc(v_recordedDeps_2992_);
lean_inc(v_traceState_2991_);
lean_inc(v_auxDeclNGen_2990_);
lean_inc(v_ngen_2989_);
lean_inc(v_nextMacroScope_2988_);
lean_inc(v_env_2987_);
lean_dec(v___x_2986_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3148_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
lean_inc(v_name_2953_);
v___x_2999_ = l_Lean_addProtected(v_env_2987_, v_name_2953_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 5, v___x_2920_);
lean_ctor_set(v___x_2997_, 0, v___x_2999_);
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_nextMacroScope_2988_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_ngen_2989_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_auxDeclNGen_2990_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_traceState_2991_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_recordedDeps_2992_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v_messages_2993_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_infoState_2994_);
lean_ctor_set(v_reuseFailAlloc_3147_, 9, v_snapshotTasks_2995_);
v___x_3001_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v_mctx_3004_; lean_object* v_zetaDeltaFVarIds_3005_; lean_object* v_postponed_3006_; lean_object* v_diag_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3145_; 
v___x_3002_ = lean_st_ref_put(v___y_2853_, v___x_3001_);
v___x_3003_ = lean_st_ref_take(v___y_2851_);
v_mctx_3004_ = lean_ctor_get(v___x_3003_, 0);
v_zetaDeltaFVarIds_3005_ = lean_ctor_get(v___x_3003_, 2);
v_postponed_3006_ = lean_ctor_get(v___x_3003_, 3);
v_diag_3007_ = lean_ctor_get(v___x_3003_, 4);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v___x_3003_, 1);
lean_dec(v_unused_3146_);
v___x_3009_ = v___x_3003_;
v_isShared_3010_ = v_isSharedCheck_3145_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_diag_3007_);
lean_inc(v_postponed_3006_);
lean_inc(v_zetaDeltaFVarIds_3005_);
lean_inc(v_mctx_3004_);
lean_dec(v___x_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3145_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_2932_);
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_mctx_3004_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3144_, 2, v_zetaDeltaFVarIds_3005_);
lean_ctor_set(v_reuseFailAlloc_3144_, 3, v_postponed_3006_);
lean_ctor_set(v_reuseFailAlloc_3144_, 4, v_diag_3007_);
v___x_3012_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3013_ = lean_st_ref_put(v___y_2851_, v___x_3012_);
v___x_3014_ = l_Lean_Expr_const___override(v_name_2953_, v___x_2845_);
v___x_3015_ = l_Lean_mkAppN(v___x_3014_, v___x_2877_);
v___x_3016_ = lean_array_get(v___x_2840_, v_fs_2849_, v_val_2841_);
lean_dec_ref(v_fs_2849_);
v___x_3017_ = l_Lean_mkAppN(v___x_3016_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_3018_ = l_Lean_Meta_mkPProdSndM(v___x_2937_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_Expr_app___override(v___x_3017_, v_a_3019_);
v___x_3021_ = l_Lean_Meta_mkEq(v___x_3015_, v___x_3020_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_n(v_a_3022_, 2);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = lean_box(0);
v___x_3024_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3022_, v___x_3023_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v___x_3026_ = l_Lean_Expr_mvarId_x21(v_a_3025_);
v___x_3027_ = l_Lean_Expr_fvarId_x21(v___x_2838_);
lean_dec_ref(v___x_2838_);
v___x_3028_ = lean_mk_empty_array_with_capacity(v___x_2847_);
v___x_3029_ = lean_box(0);
v___x_3030_ = l_Lean_MVarId_cases(v___x_3026_, v___x_3027_, v___x_3028_, v___x_2885_, v___x_3029_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; size_t v_sz_3033_; lean_object* v___x_3034_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = lean_box(0);
v_sz_3033_ = lean_array_size(v_a_3031_);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3031_, v_sz_3033_, v___x_2860_, v___x_3032_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v_a_3031_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3035_; lean_object* v_a_3036_; lean_object* v___x_3037_; 
lean_dec_ref_known(v___x_3034_, 1);
v___x_3035_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3025_, v___y_2851_);
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref(v___x_3035_);
v___x_3037_ = l_Lean_Meta_mkForallFVars(v___x_2877_, v_a_3022_, v___x_2885_, v___x_2842_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = l_Lean_Meta_mkLambdaFVars(v___x_2877_, v_a_3036_, v___x_2885_, v___x_2842_, v___x_2885_, v___x_2842_, v___x_2886_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec_ref(v___x_2877_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3042_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
lean_inc(v_brecOnEqName_2848_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 2, v_a_3038_);
lean_ctor_set(v___x_2955_, 1, v_levelParams_2844_);
lean_ctor_set(v___x_2955_, 0, v_brecOnEqName_2848_);
v___x_3042_ = v___x_2955_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_brecOnEqName_2848_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_levelParams_2844_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_a_3038_);
v___x_3042_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = lean_box(0);
lean_inc(v_brecOnEqName_2848_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 1);
lean_ctor_set(v___x_2865_, 1, v___x_3043_);
lean_ctor_set(v___x_2865_, 0, v_brecOnEqName_2848_);
v___x_3045_ = v___x_2865_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_brecOnEqName_2848_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
lean_object* v___x_3047_; 
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 2, v___x_3045_);
lean_ctor_set(v___x_2903_, 1, v_a_3040_);
lean_ctor_set(v___x_2903_, 0, v___x_3042_);
v___x_3047_ = v___x_2903_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v_a_3040_);
lean_ctor_set(v_reuseFailAlloc_3093_, 2, v___x_3045_);
v___x_3047_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; lean_object* v_a_3049_; lean_object* v___x_3050_; 
v___x_3048_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3047_, v___y_2853_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = l_Lean_addDecl(v_a_3049_, v___x_2885_, v___y_2852_, v___y_2853_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3091_; 
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v___x_3050_, 0);
lean_dec(v_unused_3092_);
v___x_3052_ = v___x_3050_;
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v___x_3050_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v_env_3055_; lean_object* v_nextMacroScope_3056_; lean_object* v_ngen_3057_; lean_object* v_auxDeclNGen_3058_; lean_object* v_traceState_3059_; lean_object* v_recordedDeps_3060_; lean_object* v_messages_3061_; lean_object* v_infoState_3062_; lean_object* v_snapshotTasks_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3089_; 
v___x_3054_ = lean_st_ref_take(v___y_2853_);
v_env_3055_ = lean_ctor_get(v___x_3054_, 0);
v_nextMacroScope_3056_ = lean_ctor_get(v___x_3054_, 1);
v_ngen_3057_ = lean_ctor_get(v___x_3054_, 2);
v_auxDeclNGen_3058_ = lean_ctor_get(v___x_3054_, 3);
v_traceState_3059_ = lean_ctor_get(v___x_3054_, 4);
v_recordedDeps_3060_ = lean_ctor_get(v___x_3054_, 6);
v_messages_3061_ = lean_ctor_get(v___x_3054_, 7);
v_infoState_3062_ = lean_ctor_get(v___x_3054_, 8);
v_snapshotTasks_3063_ = lean_ctor_get(v___x_3054_, 9);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3054_, 5);
lean_dec(v_unused_3090_);
v___x_3065_ = v___x_3054_;
v_isShared_3066_ = v_isSharedCheck_3089_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_snapshotTasks_3063_);
lean_inc(v_infoState_3062_);
lean_inc(v_messages_3061_);
lean_inc(v_recordedDeps_3060_);
lean_inc(v_traceState_3059_);
lean_inc(v_auxDeclNGen_3058_);
lean_inc(v_ngen_3057_);
lean_inc(v_nextMacroScope_3056_);
lean_inc(v_env_3055_);
lean_dec(v___x_3054_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3089_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3067_ = l_Lean_addProtected(v_env_3055_, v_brecOnEqName_2848_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 5, v___x_2920_);
lean_ctor_set(v___x_3065_, 0, v___x_3067_);
v___x_3069_ = v___x_3065_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_nextMacroScope_3056_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_ngen_3057_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_auxDeclNGen_3058_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_traceState_3059_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3088_, 6, v_recordedDeps_3060_);
lean_ctor_set(v_reuseFailAlloc_3088_, 7, v_messages_3061_);
lean_ctor_set(v_reuseFailAlloc_3088_, 8, v_infoState_3062_);
lean_ctor_set(v_reuseFailAlloc_3088_, 9, v_snapshotTasks_3063_);
v___x_3069_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_mctx_3072_; lean_object* v_zetaDeltaFVarIds_3073_; lean_object* v_postponed_3074_; lean_object* v_diag_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3086_; 
v___x_3070_ = lean_st_ref_put(v___y_2853_, v___x_3069_);
v___x_3071_ = lean_st_ref_take(v___y_2851_);
v_mctx_3072_ = lean_ctor_get(v___x_3071_, 0);
v_zetaDeltaFVarIds_3073_ = lean_ctor_get(v___x_3071_, 2);
v_postponed_3074_ = lean_ctor_get(v___x_3071_, 3);
v_diag_3075_ = lean_ctor_get(v___x_3071_, 4);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___x_3071_, 1);
lean_dec(v_unused_3087_);
v___x_3077_ = v___x_3071_;
v_isShared_3078_ = v_isSharedCheck_3086_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_diag_3075_);
lean_inc(v_postponed_3074_);
lean_inc(v_zetaDeltaFVarIds_3073_);
lean_inc(v_mctx_3072_);
lean_dec(v___x_3071_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3086_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_2932_);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_mctx_3072_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_2932_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v_zetaDeltaFVarIds_3073_);
lean_ctor_set(v_reuseFailAlloc_3085_, 3, v_postponed_3074_);
lean_ctor_set(v_reuseFailAlloc_3085_, 4, v_diag_3075_);
v___x_3080_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3081_ = lean_st_ref_put(v___y_2851_, v___x_3080_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3032_);
v___x_3083_ = v___x_3052_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3032_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2848_);
return v___x_3050_;
}
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3038_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
v_a_3096_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3039_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3039_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3036_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
v_a_3104_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3037_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3037_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_dec(v_a_3025_);
lean_dec(v_a_3022_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
return v___x_3034_;
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3025_);
lean_dec(v_a_3022_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
v_a_3112_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3030_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3030_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_a_3022_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3120_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3024_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3024_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3128_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3021_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3021_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3015_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3136_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3018_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3018_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
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
lean_dec(v_a_2945_);
lean_dec_ref(v___x_2937_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_a_2941_);
lean_dec_ref(v___x_2937_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3161_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_2942_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_2942_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref(v___x_2937_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3169_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_2940_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_2940_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
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
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v___x_2937_);
lean_del_object(v___x_2903_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec_ref(v___x_2838_);
v_a_3177_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_2938_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_2938_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
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
lean_dec(v_a_2893_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_a_2888_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
v_a_3196_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_2889_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_2889_);
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
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2871_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
v_a_3204_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_2887_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_2887_);
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
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2871_);
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
v_a_3212_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_2883_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_2883_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_del_object(v___x_2865_);
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2836_);
lean_dec_ref(v___x_2832_);
lean_dec_ref(v___x_2830_);
v_a_3220_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_2868_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_2868_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_fs_2849_);
lean_dec(v_brecOnEqName_2848_);
lean_dec(v_brecOnName_2846_);
lean_dec(v___x_2845_);
lean_dec(v_levelParams_2844_);
lean_dec(v_brecOnGoName_2843_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2836_);
lean_dec_ref(v___x_2832_);
lean_dec_ref(v___x_2830_);
lean_dec(v___x_2827_);
v_a_3230_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_2861_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_2861_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3238_ = _args[0];
lean_object* v_tail_3239_ = _args[1];
lean_object* v_recName_3240_ = _args[2];
lean_object* v___x_3241_ = _args[3];
lean_object* v___x_3242_ = _args[4];
lean_object* v___x_3243_ = _args[5];
lean_object* v___x_3244_ = _args[6];
lean_object* v___x_3245_ = _args[7];
lean_object* v___x_3246_ = _args[8];
lean_object* v___x_3247_ = _args[9];
lean_object* v___x_3248_ = _args[10];
lean_object* v___x_3249_ = _args[11];
lean_object* v___x_3250_ = _args[12];
lean_object* v___x_3251_ = _args[13];
lean_object* v_val_3252_ = _args[14];
lean_object* v___x_3253_ = _args[15];
lean_object* v_brecOnGoName_3254_ = _args[16];
lean_object* v_levelParams_3255_ = _args[17];
lean_object* v___x_3256_ = _args[18];
lean_object* v_brecOnName_3257_ = _args[19];
lean_object* v___x_3258_ = _args[20];
lean_object* v_brecOnEqName_3259_ = _args[21];
lean_object* v_fs_3260_ = _args[22];
lean_object* v___y_3261_ = _args[23];
lean_object* v___y_3262_ = _args[24];
lean_object* v___y_3263_ = _args[25];
lean_object* v___y_3264_ = _args[26];
lean_object* v___y_3265_ = _args[27];
_start:
{
uint8_t v___x_31662__boxed_3266_; lean_object* v_res_3267_; 
v___x_31662__boxed_3266_ = lean_unbox(v___x_3253_);
v_res_3267_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3238_, v_tail_3239_, v_recName_3240_, v___x_3241_, v___x_3242_, v___x_3243_, v___x_3244_, v___x_3245_, v___x_3246_, v___x_3247_, v___x_3248_, v___x_3249_, v___x_3250_, v___x_3251_, v_val_3252_, v___x_31662__boxed_3266_, v_brecOnGoName_3254_, v_levelParams_3255_, v___x_3256_, v_brecOnName_3257_, v___x_3258_, v_brecOnEqName_3259_, v_fs_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___x_3258_);
lean_dec(v_val_3252_);
lean_dec_ref(v___x_3251_);
lean_dec(v___x_3250_);
lean_dec_ref(v___x_3246_);
lean_dec(v___x_3245_);
lean_dec(v___x_3244_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3268_, lean_object* v_a_3269_, uint8_t v___x_3270_, lean_object* v_f_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; 
lean_inc_ref(v_targs_3268_);
v___x_3277_ = lean_array_push(v_targs_3268_, v_f_3271_);
v___x_3278_ = l_Lean_mkAppN(v_a_3269_, v_targs_3268_);
lean_dec_ref(v_targs_3268_);
v___x_3279_ = 0;
v___x_3280_ = 1;
v___x_3281_ = l_Lean_Meta_mkForallFVars(v___x_3277_, v___x_3278_, v___x_3279_, v___x_3270_, v___x_3270_, v___x_3280_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec_ref(v___x_3277_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3282_, lean_object* v_a_3283_, lean_object* v___x_3284_, lean_object* v_f_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
uint8_t v___x_32377__boxed_3291_; lean_object* v_res_3292_; 
v___x_32377__boxed_3291_ = lean_unbox(v___x_3284_);
v_res_3292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3282_, v_a_3283_, v___x_32377__boxed_3291_, v_f_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3296_, uint8_t v___x_3297_, lean_object* v___x_3298_, lean_object* v_targs_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; lean_object* v___f_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3306_ = lean_box(v___x_3297_);
lean_inc_ref(v_targs_3299_);
v___f_3307_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3307_, 0, v_targs_3299_);
lean_closure_set(v___f_3307_, 1, v_a_3296_);
lean_closure_set(v___f_3307_, 2, v___x_3306_);
v___x_3308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3309_ = l_Lean_mkAppN(v___x_3298_, v_targs_3299_);
lean_dec_ref(v_targs_3299_);
v___x_3310_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3308_, v___x_3309_, v___f_3307_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3311_, lean_object* v___x_3312_, lean_object* v___x_3313_, lean_object* v_targs_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v___x_32411__boxed_3321_; lean_object* v_res_3322_; 
v___x_32411__boxed_3321_ = lean_unbox(v___x_3312_);
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3311_, v___x_32411__boxed_3321_, v___x_3313_, v_targs_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec_ref(v_x_3315_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3323_, lean_object* v_x_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3323_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3331_, lean_object* v_x_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3331_, v_x_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v_x_3332_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3340_, lean_object* v___x_3341_, lean_object* v_as_3342_, size_t v_sz_3343_, size_t v_i_3344_, lean_object* v_b_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_3351_; 
v___x_3351_ = lean_usize_dec_lt(v_i_3344_, v_sz_3343_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_b_3345_);
return v___x_3352_;
}
else
{
lean_object* v_snd_3353_; lean_object* v_fst_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3451_; 
v_snd_3353_ = lean_ctor_get(v_b_3345_, 1);
v_fst_3354_ = lean_ctor_get(v_b_3345_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_b_3345_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3356_ = v_b_3345_;
v_isShared_3357_ = v_isSharedCheck_3451_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3353_);
lean_inc(v_fst_3354_);
lean_dec(v_b_3345_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3451_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3450_; 
v_fst_3358_ = lean_ctor_get(v_snd_3353_, 0);
v_snd_3359_ = lean_ctor_get(v_snd_3353_, 1);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_snd_3353_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3361_ = v_snd_3353_;
v_isShared_3362_ = v_isSharedCheck_3450_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_snd_3359_);
lean_inc(v_fst_3358_);
lean_dec(v_snd_3353_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3450_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_next_3371_; 
v_next_3371_ = lean_ctor_get(v_snd_3359_, 0);
lean_inc(v_next_3371_);
if (lean_obj_tag(v_next_3371_) == 0)
{
goto v___jp_3363_;
}
else
{
lean_object* v_upperBound_3372_; lean_object* v_val_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3449_; 
v_upperBound_3372_ = lean_ctor_get(v_snd_3359_, 1);
v_val_3373_ = lean_ctor_get(v_next_3371_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_next_3371_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3375_ = v_next_3371_;
v_isShared_3376_ = v_isSharedCheck_3449_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_val_3373_);
lean_dec(v_next_3371_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3449_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint8_t v___x_3377_; 
v___x_3377_ = lean_nat_dec_lt(v_val_3373_, v_upperBound_3372_);
if (v___x_3377_ == 0)
{
lean_del_object(v___x_3375_);
lean_dec(v_val_3373_);
goto v___jp_3363_;
}
else
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3446_; 
lean_inc(v_upperBound_3372_);
lean_del_object(v___x_3361_);
lean_del_object(v___x_3356_);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_snd_3359_);
if (v_isSharedCheck_3446_ == 0)
{
lean_object* v_unused_3447_; lean_object* v_unused_3448_; 
v_unused_3447_ = lean_ctor_get(v_snd_3359_, 1);
lean_dec(v_unused_3447_);
v_unused_3448_ = lean_ctor_get(v_snd_3359_, 0);
lean_dec(v_unused_3448_);
v___x_3379_ = v_snd_3359_;
v_isShared_3380_ = v_isSharedCheck_3446_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_snd_3359_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3446_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_array_3381_; lean_object* v_start_3382_; lean_object* v_stop_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3387_; 
v_array_3381_ = lean_ctor_get(v_fst_3358_, 0);
v_start_3382_ = lean_ctor_get(v_fst_3358_, 1);
v_stop_3383_ = lean_ctor_get(v_fst_3358_, 2);
v___x_3384_ = lean_unsigned_to_nat(1u);
v___x_3385_ = lean_nat_add(v_val_3373_, v___x_3384_);
lean_dec(v_val_3373_);
lean_inc(v___x_3385_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3385_);
v___x_3387_ = v___x_3375_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3389_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3387_);
v___x_3389_ = v___x_3379_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_upperBound_3372_);
v___x_3389_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_nat_dec_lt(v_start_3382_, v_stop_3383_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v___x_3385_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_fst_3358_);
lean_ctor_set(v___x_3391_, 1, v___x_3389_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_fst_3354_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
return v___x_3393_;
}
else
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3440_; 
lean_inc(v_stop_3383_);
lean_inc(v_start_3382_);
lean_inc_ref(v_array_3381_);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_fst_3358_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; lean_object* v_unused_3442_; lean_object* v_unused_3443_; 
v_unused_3441_ = lean_ctor_get(v_fst_3358_, 2);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_fst_3358_, 1);
lean_dec(v_unused_3442_);
v_unused_3443_ = lean_ctor_get(v_fst_3358_, 0);
lean_dec(v_unused_3443_);
v___x_3395_ = v_fst_3358_;
v_isShared_3396_ = v_isSharedCheck_3440_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v_fst_3358_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3440_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
uint8_t v___x_3397_; lean_object* v_a_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v___x_3397_ = lean_nat_dec_lt(v___x_3340_, v___x_3341_);
v_a_3398_ = lean_array_uget_borrowed(v_as_3342_, v_i_3344_);
v___x_3399_ = lean_array_fget_borrowed(v_array_3381_, v_start_3382_);
v___x_3400_ = lean_box(v___x_3397_);
lean_inc(v___x_3399_);
lean_inc(v_a_3398_);
v___f_3401_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3401_, 0, v_a_3398_);
lean_closure_set(v___f_3401_, 1, v___x_3400_);
lean_closure_set(v___f_3401_, 2, v___x_3399_);
v___x_3402_ = lean_nat_add(v_start_3382_, v___x_3384_);
lean_dec(v_start_3382_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 1, v___x_3402_);
v___x_3404_ = v___x_3395_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_array_3381_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_stop_3383_);
v___x_3404_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; 
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v_a_3398_);
v___x_3405_ = lean_infer_type(v_a_3398_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
v___x_3407_ = 0;
v___x_3408_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3406_, v___f_3401_, v___x_3407_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; size_t v___x_3420_; size_t v___x_3421_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref_known(v___x_3408_, 1);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3410_, 0, v_a_3409_);
v___x_3411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3412_ = l_Nat_reprFast(v___x_3385_);
v___x_3413_ = lean_string_append(v___x_3411_, v___x_3412_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = lean_box(0);
v___x_3415_ = l_Lean_Name_str___override(v___x_3414_, v___x_3413_);
v___x_3416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___f_3410_);
v___x_3417_ = lean_array_push(v_fst_3354_, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3404_);
lean_ctor_set(v___x_3418_, 1, v___x_3389_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = ((size_t)1ULL);
v___x_3421_ = lean_usize_add(v_i_3344_, v___x_3420_);
v_i_3344_ = v___x_3421_;
v_b_3345_ = v___x_3419_;
goto _start;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v___x_3404_);
lean_dec_ref(v___x_3389_);
lean_dec(v___x_3385_);
lean_dec(v_fst_3354_);
v_a_3423_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3408_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3408_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec_ref(v___x_3404_);
lean_dec_ref(v___f_3401_);
lean_dec_ref(v___x_3389_);
lean_dec(v___x_3385_);
lean_dec(v_fst_3354_);
v_a_3431_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3405_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3405_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
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
v___jp_3363_:
{
lean_object* v___x_3365_; 
if (v_isShared_3362_ == 0)
{
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_fst_3358_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_snd_3359_);
v___x_3365_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v___x_3365_);
v___x_3367_ = v___x_3356_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_fst_3354_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3452_, lean_object* v___x_3453_, lean_object* v_as_3454_, lean_object* v_sz_3455_, lean_object* v_i_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
size_t v_sz_boxed_3463_; size_t v_i_boxed_3464_; lean_object* v_res_3465_; 
v_sz_boxed_3463_ = lean_unbox_usize(v_sz_3455_);
lean_dec(v_sz_3455_);
v_i_boxed_3464_ = lean_unbox_usize(v_i_3456_);
lean_dec(v_i_3456_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3452_, v___x_3453_, v_as_3454_, v_sz_boxed_3463_, v_i_boxed_3464_, v_b_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v_as_3454_);
lean_dec(v___x_3453_);
lean_dec(v___x_3452_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3466_, size_t v_i_3467_, lean_object* v_bs_3468_){
_start:
{
uint8_t v___x_3469_; 
v___x_3469_ = lean_usize_dec_lt(v_i_3467_, v_sz_3466_);
if (v___x_3469_ == 0)
{
return v_bs_3468_;
}
else
{
lean_object* v_v_3470_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3488_; 
v_v_3470_ = lean_array_uget(v_bs_3468_, v_i_3467_);
v_fst_3471_ = lean_ctor_get(v_v_3470_, 0);
v_snd_3472_ = lean_ctor_get(v_v_3470_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_v_3470_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3474_ = v_v_3470_;
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_snd_3472_);
lean_inc(v_fst_3471_);
lean_dec(v_v_3470_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v_bs_x27_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___x_3476_ = lean_unsigned_to_nat(0u);
v_bs_x27_3477_ = lean_array_uset(v_bs_3468_, v_i_3467_, v___x_3476_);
v___x_3478_ = 0;
v___x_3479_ = lean_box(v___x_3478_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3479_);
v___x_3481_ = v___x_3474_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_snd_3472_);
v___x_3481_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; size_t v___x_3483_; size_t v___x_3484_; lean_object* v___x_3485_; 
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v_fst_3471_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = ((size_t)1ULL);
v___x_3484_ = lean_usize_add(v_i_3467_, v___x_3483_);
v___x_3485_ = lean_array_uset(v_bs_x27_3477_, v_i_3467_, v___x_3482_);
v_i_3467_ = v___x_3484_;
v_bs_3468_ = v___x_3485_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3489_, lean_object* v_i_3490_, lean_object* v_bs_3491_){
_start:
{
size_t v_sz_boxed_3492_; size_t v_i_boxed_3493_; lean_object* v_res_3494_; 
v_sz_boxed_3492_ = lean_unbox_usize(v_sz_3489_);
lean_dec(v_sz_3489_);
v_i_boxed_3493_ = lean_unbox_usize(v_i_3490_);
lean_dec(v_i_3490_);
v_res_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3492_, v_i_boxed_3493_, v_bs_3491_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3495_, lean_object* v___x_3496_, lean_object* v_a_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v___x_31205__overap_3503_; lean_object* v___x_3504_; 
v___x_31205__overap_3503_ = l_instInhabitedOfMonad___redArg(v___x_3495_, v___x_3496_);
lean_inc(v___y_3501_);
lean_inc_ref(v___y_3500_);
lean_inc(v___y_3499_);
lean_inc_ref(v___y_3498_);
v___x_3504_ = lean_apply_5(v___x_31205__overap_3503_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, lean_box(0));
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v_a_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3505_, v___x_3506_, v_a_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v_a_3507_);
return v_res_3513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_instMonadEIO___redArg();
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3515_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3516_ = l_StateRefT_x27_instMonad___redArg(v___x_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3521_, lean_object* v_declInfos_3522_, lean_object* v_k_3523_, lean_object* v_kind_3524_, lean_object* v_b_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
uint8_t v_kind_boxed_3531_; lean_object* v_res_3532_; 
v_kind_boxed_3531_ = lean_unbox(v_kind_3524_);
v_res_3532_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3521_, v_declInfos_3522_, v_k_3523_, v_kind_boxed_3531_, v_b_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3533_, lean_object* v_declInfos_3534_, lean_object* v_k_3535_, uint8_t v_kind_3536_, lean_object* v_name_3537_, uint8_t v_bi_3538_, lean_object* v_type_3539_, uint8_t v_kind_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v___x_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; 
v___x_3546_ = lean_box(v_kind_3536_);
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3547_, 0, v_acc_3533_);
lean_closure_set(v___f_3547_, 1, v_declInfos_3534_);
lean_closure_set(v___f_3547_, 2, v_k_3535_);
lean_closure_set(v___f_3547_, 3, v___x_3546_);
v___x_3548_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3537_, v_bi_3538_, v_type_3539_, v___f_3547_, v_kind_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
v_a_3557_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3548_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3548_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3565_, lean_object* v_k_3566_, uint8_t v_kind_3567_, lean_object* v_acc_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; lean_object* v_toApplicative_3575_; lean_object* v_toFunctor_3576_; lean_object* v_toSeq_3577_; lean_object* v_toSeqLeft_3578_; lean_object* v_toSeqRight_3579_; lean_object* v___f_3580_; lean_object* v___f_3581_; lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___x_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_toApplicative_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3647_; 
v___x_3574_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3575_ = lean_ctor_get(v___x_3574_, 0);
v_toFunctor_3576_ = lean_ctor_get(v_toApplicative_3575_, 0);
v_toSeq_3577_ = lean_ctor_get(v_toApplicative_3575_, 2);
v_toSeqLeft_3578_ = lean_ctor_get(v_toApplicative_3575_, 3);
v_toSeqRight_3579_ = lean_ctor_get(v_toApplicative_3575_, 4);
v___f_3580_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3581_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3576_, 2);
v___f_3582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3582_, 0, v_toFunctor_3576_);
v___f_3583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3583_, 0, v_toFunctor_3576_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___f_3582_);
lean_ctor_set(v___x_3584_, 1, v___f_3583_);
lean_inc(v_toSeqRight_3579_);
v___f_3585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3585_, 0, v_toSeqRight_3579_);
lean_inc(v_toSeqLeft_3578_);
v___f_3586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3586_, 0, v_toSeqLeft_3578_);
lean_inc(v_toSeq_3577_);
v___f_3587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3587_, 0, v_toSeq_3577_);
v___x_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3584_);
lean_ctor_set(v___x_3588_, 1, v___f_3580_);
lean_ctor_set(v___x_3588_, 2, v___f_3587_);
lean_ctor_set(v___x_3588_, 3, v___f_3586_);
lean_ctor_set(v___x_3588_, 4, v___f_3585_);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___f_3581_);
v___x_3590_ = l_StateRefT_x27_instMonad___redArg(v___x_3589_);
v_toApplicative_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v___x_3590_, 1);
lean_dec(v_unused_3648_);
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3647_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_toApplicative_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3647_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v_toFunctor_3595_; lean_object* v_toSeq_3596_; lean_object* v_toSeqLeft_3597_; lean_object* v_toSeqRight_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3645_; 
v_toFunctor_3595_ = lean_ctor_get(v_toApplicative_3591_, 0);
v_toSeq_3596_ = lean_ctor_get(v_toApplicative_3591_, 2);
v_toSeqLeft_3597_ = lean_ctor_get(v_toApplicative_3591_, 3);
v_toSeqRight_3598_ = lean_ctor_get(v_toApplicative_3591_, 4);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_toApplicative_3591_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; 
v_unused_3646_ = lean_ctor_get(v_toApplicative_3591_, 1);
lean_dec(v_unused_3646_);
v___x_3600_ = v_toApplicative_3591_;
v_isShared_3601_ = v_isSharedCheck_3645_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_toSeqRight_3598_);
lean_inc(v_toSeqLeft_3597_);
lean_inc(v_toSeq_3596_);
lean_inc(v_toFunctor_3595_);
lean_dec(v_toApplicative_3591_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3645_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___f_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___x_3606_; lean_object* v___f_3607_; lean_object* v___f_3608_; lean_object* v___f_3609_; lean_object* v___x_3611_; 
v___f_3602_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3603_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3595_);
v___f_3604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3604_, 0, v_toFunctor_3595_);
v___f_3605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3605_, 0, v_toFunctor_3595_);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___f_3604_);
lean_ctor_set(v___x_3606_, 1, v___f_3605_);
v___f_3607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3607_, 0, v_toSeqRight_3598_);
v___f_3608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3608_, 0, v_toSeqLeft_3597_);
v___f_3609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3609_, 0, v_toSeq_3596_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 4, v___f_3607_);
lean_ctor_set(v___x_3600_, 3, v___f_3608_);
lean_ctor_set(v___x_3600_, 2, v___f_3609_);
lean_ctor_set(v___x_3600_, 1, v___f_3602_);
lean_ctor_set(v___x_3600_, 0, v___x_3606_);
v___x_3611_ = v___x_3600_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v___f_3602_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v___f_3609_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v___f_3608_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v___f_3607_);
v___x_3611_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; 
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 1, v___f_3603_);
lean_ctor_set(v___x_3593_, 0, v___x_3611_);
v___x_3613_ = v___x_3593_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___f_3603_);
v___x_3613_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3614_ = lean_array_get_size(v_acc_3568_);
v___x_3615_ = lean_array_get_size(v_declInfos_3565_);
v___x_3616_ = lean_nat_dec_lt(v___x_3614_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
lean_dec_ref(v___x_3613_);
lean_dec_ref(v_declInfos_3565_);
lean_inc(v___y_3572_);
lean_inc_ref(v___y_3571_);
lean_inc(v___y_3570_);
lean_inc_ref(v___y_3569_);
v___x_3617_ = lean_apply_6(v_k_3566_, v_acc_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, lean_box(0));
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v_snd_3627_; lean_object* v_fst_3628_; lean_object* v_fst_3629_; lean_object* v_snd_3630_; lean_object* v___x_3631_; 
v___x_3618_ = lean_box(0);
v___x_3619_ = 0;
v___x_3620_ = l_Lean_instInhabitedExpr;
v___f_3621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3621_, 0, v___x_3613_);
lean_closure_set(v___f_3621_, 1, v___x_3620_);
v___f_3622_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3622_, 0, v___f_3621_);
v___x_3623_ = lean_box(v___x_3619_);
v___x_3624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
lean_ctor_set(v___x_3624_, 1, v___f_3622_);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3618_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_array_get(v___x_3625_, v_declInfos_3565_, v___x_3614_);
lean_dec_ref_known(v___x_3625_, 2);
v_snd_3627_ = lean_ctor_get(v___x_3626_, 1);
lean_inc(v_snd_3627_);
v_fst_3628_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_fst_3628_);
lean_dec(v___x_3626_);
v_fst_3629_ = lean_ctor_get(v_snd_3627_, 0);
lean_inc(v_fst_3629_);
v_snd_3630_ = lean_ctor_get(v_snd_3627_, 1);
lean_inc(v_snd_3630_);
lean_dec(v_snd_3627_);
lean_inc(v___y_3572_);
lean_inc_ref(v___y_3571_);
lean_inc(v___y_3570_);
lean_inc_ref(v___y_3569_);
lean_inc_ref(v_acc_3568_);
v___x_3631_ = lean_apply_6(v_snd_3630_, v_acc_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, lean_box(0));
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v___x_3633_ = lean_unbox(v_fst_3629_);
lean_dec(v_fst_3629_);
v___x_3634_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3568_, v_declInfos_3565_, v_k_3566_, v_kind_3567_, v_fst_3628_, v___x_3633_, v_a_3632_, v_kind_3567_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
return v___x_3634_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec(v_fst_3629_);
lean_dec(v_fst_3628_);
lean_dec_ref(v_acc_3568_);
lean_dec_ref(v_k_3566_);
lean_dec_ref(v_declInfos_3565_);
v_a_3635_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3631_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3631_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3649_, lean_object* v_declInfos_3650_, lean_object* v_k_3651_, uint8_t v_kind_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_array_push(v_acc_3649_, v_b_3653_);
v___x_3660_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3650_, v_k_3651_, v_kind_3652_, v___x_3659_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3661_, lean_object* v_declInfos_3662_, lean_object* v_k_3663_, lean_object* v_kind_3664_, lean_object* v_name_3665_, lean_object* v_bi_3666_, lean_object* v_type_3667_, lean_object* v_kind_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v_kind_boxed_3674_; uint8_t v_bi_boxed_3675_; uint8_t v_kind_boxed_3676_; lean_object* v_res_3677_; 
v_kind_boxed_3674_ = lean_unbox(v_kind_3664_);
v_bi_boxed_3675_ = lean_unbox(v_bi_3666_);
v_kind_boxed_3676_ = lean_unbox(v_kind_3668_);
v_res_3677_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3661_, v_declInfos_3662_, v_k_3663_, v_kind_boxed_3674_, v_name_3665_, v_bi_boxed_3675_, v_type_3667_, v_kind_boxed_3676_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3678_, lean_object* v_k_3679_, lean_object* v_kind_3680_, lean_object* v_acc_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
uint8_t v_kind_boxed_3687_; lean_object* v_res_3688_; 
v_kind_boxed_3687_ = lean_unbox(v_kind_3680_);
v_res_3688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3678_, v_k_3679_, v_kind_boxed_3687_, v_acc_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3689_, lean_object* v_k_3690_, uint8_t v_kind_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3698_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3689_, v_k_3690_, v_kind_3691_, v___x_3697_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3699_, lean_object* v_k_3700_, lean_object* v_kind_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_kind_boxed_3707_; lean_object* v_res_3708_; 
v_kind_boxed_3707_ = lean_unbox(v_kind_3701_);
v_res_3708_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3699_, v_k_3700_, v_kind_boxed_3707_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3709_, lean_object* v_k_3710_, uint8_t v_kind_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
size_t v_sz_3717_; size_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_sz_3717_ = lean_array_size(v_declInfos_3709_);
v___x_3718_ = ((size_t)0ULL);
v___x_3719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3717_, v___x_3718_, v_declInfos_3709_);
v___x_3720_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3719_, v_k_3710_, v_kind_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3721_, lean_object* v_k_3722_, lean_object* v_kind_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
uint8_t v_kind_boxed_3729_; lean_object* v_res_3730_; 
v_kind_boxed_3729_ = lean_unbox(v_kind_3723_);
v_res_3730_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3721_, v_k_3722_, v_kind_boxed_3729_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
return v_res_3730_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3733_ = lean_unsigned_to_nat(4u);
v___x_3734_ = lean_unsigned_to_nat(202u);
v___x_3735_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3736_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3737_ = l_mkPanicMessageWithDecl(v___x_3736_, v___x_3735_, v___x_3734_, v___x_3733_, v___x_3732_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3744_ = l_Lean_stringToMessageData(v___x_3743_);
return v___x_3744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3746_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3747_ = l_Lean_stringToMessageData(v___x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3748_, lean_object* v_numMotives_3749_, lean_object* v_numMinors_3750_, lean_object* v___x_3751_, lean_object* v_all_3752_, lean_object* v___x_3753_, lean_object* v___x_3754_, lean_object* v_head_3755_, lean_object* v_tail_3756_, lean_object* v_recName_3757_, lean_object* v_brecOnGoName_3758_, lean_object* v_levelParams_3759_, lean_object* v_brecOnName_3760_, lean_object* v_brecOnEqName_3761_, lean_object* v_type_3762_, lean_object* v_refArgs_3763_, lean_object* v_refBody_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3770_ = lean_nat_add(v_nParams_3748_, v_numMotives_3749_);
v___x_3771_ = lean_nat_add(v___x_3770_, v_numMinors_3750_);
v___x_3772_ = lean_array_get_size(v_refArgs_3763_);
v___x_3773_ = lean_nat_dec_lt(v___x_3771_, v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec(v___x_3771_);
lean_dec(v___x_3770_);
lean_dec_ref(v_refArgs_3763_);
lean_dec_ref(v_type_3762_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3753_);
lean_dec_ref(v_all_3752_);
lean_dec(v___x_3751_);
lean_dec(v_nParams_3748_);
v___x_3774_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3775_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3774_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3775_;
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3776_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3748_);
lean_inc_ref_n(v_refArgs_3763_, 2);
v___x_3777_ = l_Array_toSubarray___redArg(v_refArgs_3763_, v___x_3776_, v_nParams_3748_);
lean_inc(v___x_3770_);
v___x_3778_ = l_Array_toSubarray___redArg(v_refArgs_3763_, v_nParams_3748_, v___x_3770_);
v___x_3779_ = l_Subarray_copy___redArg(v___x_3778_);
v___x_3780_ = l_Lean_Expr_getAppFn(v_refBody_3764_);
v___x_3781_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3779_, v___x_3780_);
lean_dec_ref(v___x_3780_);
if (lean_obj_tag(v___x_3781_) == 1)
{
lean_object* v_val_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___f_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_type_3762_);
v_val_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v___x_3781_, 1);
lean_inc_n(v___x_3771_, 2);
lean_inc_ref_n(v_refArgs_3763_, 2);
v___x_3783_ = l_Array_toSubarray___redArg(v_refArgs_3763_, v___x_3770_, v___x_3771_);
v___x_3784_ = l_Subarray_copy___redArg(v___x_3777_);
v___x_3785_ = l_Subarray_copy___redArg(v___x_3783_);
v___x_3786_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3779_);
lean_inc_ref(v___x_3784_);
lean_inc(v___x_3751_);
v___f_3787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3787_, 0, v___x_3751_);
lean_closure_set(v___f_3787_, 1, v___x_3784_);
lean_closure_set(v___f_3787_, 2, v___x_3779_);
lean_closure_set(v___f_3787_, 3, v_all_3752_);
lean_closure_set(v___f_3787_, 4, v___x_3753_);
lean_closure_set(v___f_3787_, 5, v___x_3776_);
lean_closure_set(v___f_3787_, 6, v___x_3786_);
v___x_3788_ = lean_nat_sub(v___x_3772_, v___x_3786_);
lean_inc(v___x_3788_);
v___x_3789_ = l_Array_toSubarray___redArg(v_refArgs_3763_, v___x_3771_, v___x_3788_);
v___x_3790_ = l_Subarray_copy___redArg(v___x_3789_);
v___x_3791_ = lean_array_get(v___x_3754_, v_refArgs_3763_, v___x_3788_);
lean_dec(v___x_3788_);
lean_dec_ref(v_refArgs_3763_);
lean_inc(v___y_3768_);
lean_inc_ref(v___y_3767_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___x_3791_);
v___x_3792_ = lean_infer_type(v___x_3791_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
lean_inc(v___y_3768_);
lean_inc_ref(v___y_3767_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
v___x_3794_ = lean_infer_type(v_a_3793_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v___x_3796_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3795_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
if (lean_obj_tag(v_a_3797_) == 1)
{
lean_object* v_val_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___f_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; size_t v_sz_3811_; size_t v___x_3812_; lean_object* v___x_3813_; 
v_val_3798_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_val_3798_);
lean_dec_ref_known(v_a_3797_, 1);
v___x_3799_ = l_Lean_mkLevelMax(v_val_3798_, v_head_3755_);
v___x_3800_ = lean_array_get_size(v___x_3779_);
v___x_3801_ = l_Array_ofFn___redArg(v___x_3800_, v___f_3787_);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3803_ = lean_array_get_size(v___x_3801_);
lean_inc_ref(v___x_3801_);
v___x_3804_ = l_Array_toSubarray___redArg(v___x_3801_, v___x_3776_, v___x_3803_);
v___x_3805_ = lean_box(v___x_3773_);
lean_inc(v___x_3771_);
lean_inc_ref(v___x_3779_);
lean_inc_ref(v___x_3804_);
v___f_3806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3806_, 0, v___x_3799_);
lean_closure_set(v___f_3806_, 1, v_tail_3756_);
lean_closure_set(v___f_3806_, 2, v_recName_3757_);
lean_closure_set(v___f_3806_, 3, v___x_3784_);
lean_closure_set(v___f_3806_, 4, v___x_3804_);
lean_closure_set(v___f_3806_, 5, v___x_3779_);
lean_closure_set(v___f_3806_, 6, v___x_3771_);
lean_closure_set(v___f_3806_, 7, v___x_3772_);
lean_closure_set(v___f_3806_, 8, v___x_3785_);
lean_closure_set(v___f_3806_, 9, v___x_3801_);
lean_closure_set(v___f_3806_, 10, v___x_3790_);
lean_closure_set(v___f_3806_, 11, v___x_3791_);
lean_closure_set(v___f_3806_, 12, v___x_3786_);
lean_closure_set(v___f_3806_, 13, v___x_3754_);
lean_closure_set(v___f_3806_, 14, v_val_3782_);
lean_closure_set(v___f_3806_, 15, v___x_3805_);
lean_closure_set(v___f_3806_, 16, v_brecOnGoName_3758_);
lean_closure_set(v___f_3806_, 17, v_levelParams_3759_);
lean_closure_set(v___f_3806_, 18, v___x_3751_);
lean_closure_set(v___f_3806_, 19, v_brecOnName_3760_);
lean_closure_set(v___f_3806_, 20, v___x_3776_);
lean_closure_set(v___f_3806_, 21, v_brecOnEqName_3761_);
v___x_3807_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
lean_ctor_set(v___x_3808_, 1, v___x_3800_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3804_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3802_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v_sz_3811_ = lean_array_size(v___x_3779_);
v___x_3812_ = ((size_t)0ULL);
v___x_3813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3771_, v___x_3772_, v___x_3779_, v_sz_3811_, v___x_3812_, v___x_3810_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec_ref(v___x_3779_);
lean_dec(v___x_3771_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v_fst_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v_fst_3815_ = lean_ctor_get(v_a_3814_, 0);
lean_inc(v_fst_3815_);
lean_dec(v_a_3814_);
v___x_3816_ = 0;
v___x_3817_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3815_, v___f_3806_, v___x_3816_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3817_;
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___f_3806_);
v_a_3818_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3813_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3813_);
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
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec(v_a_3797_);
lean_dec_ref(v___x_3790_);
lean_dec_ref(v___f_3787_);
lean_dec_ref(v___x_3785_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v___x_3779_);
lean_dec(v___x_3771_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3751_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3827_ = l_Lean_MessageData_ofExpr(v___x_3791_);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3830_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3831_;
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v___x_3791_);
lean_dec_ref(v___x_3790_);
lean_dec_ref(v___f_3787_);
lean_dec_ref(v___x_3785_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v___x_3779_);
lean_dec(v___x_3771_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3751_);
v_a_3832_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3796_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3796_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec(v___x_3791_);
lean_dec_ref(v___x_3790_);
lean_dec_ref(v___f_3787_);
lean_dec_ref(v___x_3785_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v___x_3779_);
lean_dec(v___x_3771_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3751_);
v_a_3840_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3794_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3794_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec(v___x_3791_);
lean_dec_ref(v___x_3790_);
lean_dec_ref(v___f_3787_);
lean_dec_ref(v___x_3785_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3782_);
lean_dec_ref(v___x_3779_);
lean_dec(v___x_3771_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3751_);
v_a_3848_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3792_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3792_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec(v___x_3781_);
lean_dec_ref(v___x_3777_);
lean_dec(v___x_3771_);
lean_dec(v___x_3770_);
lean_dec_ref(v_refArgs_3763_);
lean_dec(v_brecOnEqName_3761_);
lean_dec(v_brecOnName_3760_);
lean_dec(v_levelParams_3759_);
lean_dec(v_brecOnGoName_3758_);
lean_dec(v_recName_3757_);
lean_dec(v_tail_3756_);
lean_dec(v_head_3755_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3753_);
lean_dec_ref(v_all_3752_);
lean_dec(v___x_3751_);
v___x_3856_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3857_ = l_Lean_MessageData_ofExpr(v_type_3762_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_array_to_list(v___x_3779_);
v___x_3862_ = lean_box(0);
v___x_3863_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3861_, v___x_3862_);
v___x_3864_ = l_Lean_MessageData_ofList(v___x_3863_);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3860_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3865_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3866_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3867_ = _args[0];
lean_object* v_numMotives_3868_ = _args[1];
lean_object* v_numMinors_3869_ = _args[2];
lean_object* v___x_3870_ = _args[3];
lean_object* v_all_3871_ = _args[4];
lean_object* v___x_3872_ = _args[5];
lean_object* v___x_3873_ = _args[6];
lean_object* v_head_3874_ = _args[7];
lean_object* v_tail_3875_ = _args[8];
lean_object* v_recName_3876_ = _args[9];
lean_object* v_brecOnGoName_3877_ = _args[10];
lean_object* v_levelParams_3878_ = _args[11];
lean_object* v_brecOnName_3879_ = _args[12];
lean_object* v_brecOnEqName_3880_ = _args[13];
lean_object* v_type_3881_ = _args[14];
lean_object* v_refArgs_3882_ = _args[15];
lean_object* v_refBody_3883_ = _args[16];
lean_object* v___y_3884_ = _args[17];
lean_object* v___y_3885_ = _args[18];
lean_object* v___y_3886_ = _args[19];
lean_object* v___y_3887_ = _args[20];
lean_object* v___y_3888_ = _args[21];
_start:
{
lean_object* v_res_3889_; 
v_res_3889_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3867_, v_numMotives_3868_, v_numMinors_3869_, v___x_3870_, v_all_3871_, v___x_3872_, v___x_3873_, v_head_3874_, v_tail_3875_, v_recName_3876_, v_brecOnGoName_3877_, v_levelParams_3878_, v_brecOnName_3879_, v_brecOnEqName_3880_, v_type_3881_, v_refArgs_3882_, v_refBody_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec_ref(v_refBody_3883_);
lean_dec(v_numMinors_3869_);
lean_dec(v_numMotives_3868_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3892_, lean_object* v_nParams_3893_, lean_object* v_all_3894_, lean_object* v_brecOnName_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v_brecOnGoName_3904_; lean_object* v___x_3905_; lean_object* v_brecOnEqName_3906_; lean_object* v___x_3907_; 
v___x_3901_ = l_Lean_instInhabitedExpr;
v___x_3902_ = lean_box(0);
v___x_3903_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3895_, 2);
v_brecOnGoName_3904_ = l_Lean_Name_str___override(v_brecOnName_3895_, v___x_3903_);
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3906_ = l_Lean_Name_str___override(v_brecOnName_3895_, v___x_3905_);
lean_inc(v_recName_3892_);
v___x_3907_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3892_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3935_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3935_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3935_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
if (lean_obj_tag(v_a_3908_) == 7)
{
lean_object* v_val_3912_; lean_object* v_toConstantVal_3913_; lean_object* v_numMotives_3914_; lean_object* v_numMinors_3915_; lean_object* v_levelParams_3916_; lean_object* v_type_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_del_object(v___x_3910_);
v_val_3912_ = lean_ctor_get(v_a_3908_, 0);
lean_inc_ref(v_val_3912_);
lean_dec_ref_known(v_a_3908_, 1);
v_toConstantVal_3913_ = lean_ctor_get(v_val_3912_, 0);
lean_inc_ref(v_toConstantVal_3913_);
v_numMotives_3914_ = lean_ctor_get(v_val_3912_, 4);
lean_inc(v_numMotives_3914_);
v_numMinors_3915_ = lean_ctor_get(v_val_3912_, 5);
lean_inc(v_numMinors_3915_);
lean_dec_ref(v_val_3912_);
v_levelParams_3916_ = lean_ctor_get(v_toConstantVal_3913_, 1);
lean_inc_n(v_levelParams_3916_, 2);
v_type_3917_ = lean_ctor_get(v_toConstantVal_3913_, 2);
lean_inc_ref(v_type_3917_);
lean_dec_ref(v_toConstantVal_3913_);
v___x_3918_ = lean_box(0);
v___x_3919_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3916_, v___x_3918_);
if (lean_obj_tag(v___x_3919_) == 1)
{
lean_object* v_head_3920_; lean_object* v_tail_3921_; lean_object* v___f_3922_; uint8_t v___x_3923_; lean_object* v___x_3924_; 
v_head_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_head_3920_);
v_tail_3921_ = lean_ctor_get(v___x_3919_, 1);
lean_inc(v_tail_3921_);
lean_inc_ref(v_type_3917_);
v___f_3922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3922_, 0, v_nParams_3893_);
lean_closure_set(v___f_3922_, 1, v_numMotives_3914_);
lean_closure_set(v___f_3922_, 2, v_numMinors_3915_);
lean_closure_set(v___f_3922_, 3, v___x_3919_);
lean_closure_set(v___f_3922_, 4, v_all_3894_);
lean_closure_set(v___f_3922_, 5, v___x_3902_);
lean_closure_set(v___f_3922_, 6, v___x_3901_);
lean_closure_set(v___f_3922_, 7, v_head_3920_);
lean_closure_set(v___f_3922_, 8, v_tail_3921_);
lean_closure_set(v___f_3922_, 9, v_recName_3892_);
lean_closure_set(v___f_3922_, 10, v_brecOnGoName_3904_);
lean_closure_set(v___f_3922_, 11, v_levelParams_3916_);
lean_closure_set(v___f_3922_, 12, v_brecOnName_3895_);
lean_closure_set(v___f_3922_, 13, v_brecOnEqName_3906_);
lean_closure_set(v___f_3922_, 14, v_type_3917_);
v___x_3923_ = 0;
v___x_3924_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3917_, v___f_3922_, v___x_3923_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec(v___x_3919_);
lean_dec_ref(v_type_3917_);
lean_dec(v_levelParams_3916_);
lean_dec(v_numMinors_3915_);
lean_dec(v_numMotives_3914_);
lean_dec(v_brecOnEqName_3906_);
lean_dec(v_brecOnGoName_3904_);
lean_dec(v_brecOnName_3895_);
lean_dec_ref(v_all_3894_);
lean_dec(v_nParams_3893_);
v___x_3925_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3926_ = l_Lean_MessageData_ofName(v_recName_3892_);
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3925_);
lean_ctor_set(v___x_3927_, 1, v___x_3926_);
v___x_3928_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3929_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v___x_3930_;
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3933_; 
lean_dec(v_a_3908_);
lean_dec(v_brecOnEqName_3906_);
lean_dec(v_brecOnGoName_3904_);
lean_dec(v_brecOnName_3895_);
lean_dec_ref(v_all_3894_);
lean_dec(v_nParams_3893_);
lean_dec(v_recName_3892_);
v___x_3931_ = lean_box(0);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3931_);
v___x_3933_ = v___x_3910_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3931_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
else
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3943_; 
lean_dec(v_brecOnEqName_3906_);
lean_dec(v_brecOnGoName_3904_);
lean_dec(v_brecOnName_3895_);
lean_dec_ref(v_all_3894_);
lean_dec(v_nParams_3893_);
lean_dec(v_recName_3892_);
v_a_3936_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3907_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3907_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3941_; 
if (v_isShared_3939_ == 0)
{
v___x_3941_ = v___x_3938_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
v___x_3941_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
return v___x_3941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3944_, lean_object* v_nParams_3945_, lean_object* v_all_3946_, lean_object* v_brecOnName_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3944_, v_nParams_3945_, v_all_3946_, v_brecOnName_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
lean_dec(v_a_3951_);
lean_dec_ref(v_a_3950_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3954_, lean_object* v___x_3955_, lean_object* v___x_3956_, lean_object* v___x_3957_, lean_object* v___x_3958_, lean_object* v_a_3959_, lean_object* v_b_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
uint8_t v___x_3966_; 
v___x_3966_ = lean_nat_dec_lt(v_a_3959_, v_upperBound_3954_);
if (v___x_3966_ == 0)
{
lean_object* v___x_3967_; 
lean_dec(v_a_3959_);
lean_dec_ref(v___x_3958_);
lean_dec(v___x_3957_);
lean_dec(v___x_3956_);
lean_dec(v___x_3955_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v_b_3960_);
return v___x_3967_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_unsigned_to_nat(1u);
v___x_3970_ = lean_nat_add(v_a_3959_, v___x_3969_);
lean_dec(v_a_3959_);
lean_inc_n(v___x_3970_, 2);
lean_inc(v___x_3955_);
v___x_3971_ = lean_name_append_index_after(v___x_3955_, v___x_3970_);
lean_inc(v___x_3956_);
v___x_3972_ = lean_name_append_index_after(v___x_3956_, v___x_3970_);
lean_inc_ref(v___x_3958_);
lean_inc(v___x_3957_);
v___x_3973_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3971_, v___x_3957_, v___x_3958_, v___x_3972_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_dec_ref_known(v___x_3973_, 1);
v_a_3959_ = v___x_3970_;
v_b_3960_ = v___x_3968_;
goto _start;
}
else
{
lean_dec(v___x_3970_);
lean_dec_ref(v___x_3958_);
lean_dec(v___x_3957_);
lean_dec(v___x_3956_);
lean_dec(v___x_3955_);
return v___x_3973_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v_a_3980_, lean_object* v_b_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3975_, v___x_3976_, v___x_3977_, v___x_3978_, v___x_3979_, v_a_3980_, v_b_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v_upperBound_3975_);
return v_res_3987_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3993_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3994_ = l_Lean_Name_append(v___x_3993_, v___x_3992_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_toCold_4001_; lean_object* v_options_4002_; lean_object* v_inheritedTraceOptions_4003_; uint8_t v_hasTrace_4004_; lean_object* v___x_4005_; 
v_toCold_4001_ = lean_ctor_get(v_a_3998_, 0);
v_options_4002_ = lean_ctor_get(v_toCold_4001_, 2);
v_inheritedTraceOptions_4003_ = lean_ctor_get(v_toCold_4001_, 11);
v_hasTrace_4004_ = lean_ctor_get_uint8(v_options_4002_, sizeof(void*)*1);
v___x_4005_ = lean_box(0);
if (v_hasTrace_4004_ == 0)
{
lean_object* v___x_4006_; 
lean_inc(v_indName_3995_);
v___x_4006_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4071_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4009_ = v___x_4006_;
v_isShared_4010_ = v_isSharedCheck_4071_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_4006_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4071_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
if (lean_obj_tag(v_a_4007_) == 5)
{
lean_object* v_val_4011_; uint8_t v_isRec_4012_; 
v_val_4011_ = lean_ctor_get(v_a_4007_, 0);
lean_inc_ref(v_val_4011_);
lean_dec_ref_known(v_a_4007_, 1);
v_isRec_4012_ = lean_ctor_get_uint8(v_val_4011_, sizeof(void*)*6);
if (v_isRec_4012_ == 0)
{
lean_object* v___x_4013_; lean_object* v___x_4015_; 
lean_dec_ref(v_val_4011_);
lean_dec(v_indName_3995_);
v___x_4013_ = lean_box(0);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4013_);
v___x_4015_ = v___x_4009_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
else
{
lean_object* v_toConstantVal_4017_; lean_object* v_numParams_4018_; lean_object* v_all_4019_; lean_object* v_numNested_4020_; lean_object* v_type_4021_; lean_object* v___x_4022_; 
lean_del_object(v___x_4009_);
v_toConstantVal_4017_ = lean_ctor_get(v_val_4011_, 0);
lean_inc_ref(v_toConstantVal_4017_);
v_numParams_4018_ = lean_ctor_get(v_val_4011_, 1);
lean_inc(v_numParams_4018_);
v_all_4019_ = lean_ctor_get(v_val_4011_, 3);
lean_inc(v_all_4019_);
v_numNested_4020_ = lean_ctor_get(v_val_4011_, 5);
lean_inc(v_numNested_4020_);
lean_dec_ref(v_val_4011_);
v_type_4021_ = lean_ctor_get(v_toConstantVal_4017_, 2);
lean_inc_ref(v_type_4021_);
lean_dec_ref(v_toConstantVal_4017_);
v___x_4022_ = l_Lean_Meta_isPropFormerType(v_type_4021_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4058_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4058_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4058_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_unbox(v_a_4023_);
lean_dec(v_a_4023_);
if (v___x_4027_ == 0)
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_del_object(v___x_4025_);
lean_inc_n(v_indName_3995_, 2);
v___x_4028_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4029_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4019_);
v___x_4030_ = lean_array_mk(v_all_4019_);
lean_inc(v___x_4029_);
lean_inc_ref(v___x_4030_);
lean_inc(v_numParams_4018_);
lean_inc(v___x_4028_);
v___x_4031_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4028_, v_numParams_4018_, v___x_4030_, v___x_4029_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4052_; 
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; 
v_unused_4053_ = lean_ctor_get(v___x_4031_, 0);
lean_dec(v_unused_4053_);
v___x_4033_ = v___x_4031_;
v_isShared_4034_ = v_isSharedCheck_4052_;
goto v_resetjp_4032_;
}
else
{
lean_dec(v___x_4031_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4052_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = l_List_get_x21Internal___redArg(v___x_4005_, v_all_4019_, v___x_4035_);
lean_dec(v_all_4019_);
v___x_4037_ = lean_name_eq(v___x_4036_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_dec_ref(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec(v___x_4028_);
lean_dec(v_numNested_4020_);
lean_dec(v_numParams_4018_);
v___x_4038_ = lean_box(0);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4038_);
v___x_4040_ = v___x_4033_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
else
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_del_object(v___x_4033_);
v___x_4042_ = lean_box(0);
v___x_4043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4020_, v___x_4028_, v___x_4029_, v_numParams_4018_, v___x_4030_, v___x_4035_, v___x_4042_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4020_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4050_ == 0)
{
lean_object* v_unused_4051_; 
v_unused_4051_ = lean_ctor_get(v___x_4043_, 0);
lean_dec(v_unused_4051_);
v___x_4045_ = v___x_4043_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_dec(v___x_4043_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 0, v___x_4042_);
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4042_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
else
{
return v___x_4043_;
}
}
}
}
else
{
lean_dec_ref(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec(v___x_4028_);
lean_dec(v_numNested_4020_);
lean_dec(v_all_4019_);
lean_dec(v_numParams_4018_);
lean_dec(v_indName_3995_);
return v___x_4031_;
}
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
lean_dec(v_numNested_4020_);
lean_dec(v_all_4019_);
lean_dec(v_numParams_4018_);
lean_dec(v_indName_3995_);
v___x_4054_ = lean_box(0);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4054_);
v___x_4056_ = v___x_4025_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4054_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v_numNested_4020_);
lean_dec(v_all_4019_);
lean_dec(v_numParams_4018_);
lean_dec(v_indName_3995_);
v_a_4059_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4022_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4022_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
}
else
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
lean_dec(v_a_4007_);
lean_dec(v_indName_3995_);
v___x_4067_ = lean_box(0);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4067_);
v___x_4069_ = v___x_4009_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
else
{
lean_object* v_a_4072_; lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4079_; 
lean_dec(v_indName_3995_);
v_a_4072_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4079_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4074_ = v___x_4006_;
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
else
{
lean_inc(v_a_4072_);
lean_dec(v___x_4006_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4079_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4077_; 
if (v_isShared_4075_ == 0)
{
v___x_4077_ = v___x_4074_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v_a_4072_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
}
}
else
{
lean_object* v___f_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v_a_4088_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v_a_4103_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v_a_4108_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v_a_4113_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v_a_4125_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v_a_4130_; 
lean_inc(v_indName_3995_);
v___f_4080_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4080_, 0, v_indName_3995_);
v___x_4081_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4082_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4083_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4084_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4003_, v_options_4002_, v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = l_Lean_trace_profiler;
v___x_4198_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4002_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; 
lean_dec_ref(v___f_4080_);
lean_inc(v_indName_3995_);
v___x_4199_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4264_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4264_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4264_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
if (lean_obj_tag(v_a_4200_) == 5)
{
lean_object* v_val_4204_; uint8_t v_isRec_4205_; 
v_val_4204_ = lean_ctor_get(v_a_4200_, 0);
lean_inc_ref(v_val_4204_);
lean_dec_ref_known(v_a_4200_, 1);
v_isRec_4205_ = lean_ctor_get_uint8(v_val_4204_, sizeof(void*)*6);
if (v_isRec_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
lean_dec_ref(v_val_4204_);
lean_dec(v_indName_3995_);
v___x_4206_ = lean_box(0);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4206_);
v___x_4208_ = v___x_4202_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
else
{
lean_object* v_toConstantVal_4210_; lean_object* v_numParams_4211_; lean_object* v_all_4212_; lean_object* v_numNested_4213_; lean_object* v_type_4214_; lean_object* v___x_4215_; 
lean_del_object(v___x_4202_);
v_toConstantVal_4210_ = lean_ctor_get(v_val_4204_, 0);
lean_inc_ref(v_toConstantVal_4210_);
v_numParams_4211_ = lean_ctor_get(v_val_4204_, 1);
lean_inc(v_numParams_4211_);
v_all_4212_ = lean_ctor_get(v_val_4204_, 3);
lean_inc(v_all_4212_);
v_numNested_4213_ = lean_ctor_get(v_val_4204_, 5);
lean_inc(v_numNested_4213_);
lean_dec_ref(v_val_4204_);
v_type_4214_ = lean_ctor_get(v_toConstantVal_4210_, 2);
lean_inc_ref(v_type_4214_);
lean_dec_ref(v_toConstantVal_4210_);
v___x_4215_ = l_Lean_Meta_isPropFormerType(v_type_4214_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4251_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4218_ = v___x_4215_;
v_isShared_4219_ = v_isSharedCheck_4251_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4251_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_unbox(v_a_4216_);
lean_dec(v_a_4216_);
if (v___x_4220_ == 0)
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_del_object(v___x_4218_);
lean_inc_n(v_indName_3995_, 2);
v___x_4221_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4222_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4212_);
v___x_4223_ = lean_array_mk(v_all_4212_);
lean_inc(v___x_4222_);
lean_inc_ref(v___x_4223_);
lean_inc(v_numParams_4211_);
lean_inc(v___x_4221_);
v___x_4224_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4221_, v_numParams_4211_, v___x_4223_, v___x_4222_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4245_; 
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4245_ == 0)
{
lean_object* v_unused_4246_; 
v_unused_4246_ = lean_ctor_get(v___x_4224_, 0);
lean_dec(v_unused_4246_);
v___x_4226_ = v___x_4224_;
v_isShared_4227_ = v_isSharedCheck_4245_;
goto v_resetjp_4225_;
}
else
{
lean_dec(v___x_4224_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4245_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4228_ = lean_unsigned_to_nat(0u);
v___x_4229_ = l_List_get_x21Internal___redArg(v___x_4005_, v_all_4212_, v___x_4228_);
lean_dec(v_all_4212_);
v___x_4230_ = lean_name_eq(v___x_4229_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4233_; 
lean_dec_ref(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v___x_4221_);
lean_dec(v_numNested_4213_);
lean_dec(v_numParams_4211_);
v___x_4231_ = lean_box(0);
if (v_isShared_4227_ == 0)
{
lean_ctor_set(v___x_4226_, 0, v___x_4231_);
v___x_4233_ = v___x_4226_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
lean_del_object(v___x_4226_);
v___x_4235_ = lean_box(0);
v___x_4236_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4213_, v___x_4221_, v___x_4222_, v_numParams_4211_, v___x_4223_, v___x_4228_, v___x_4235_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4213_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4243_ == 0)
{
lean_object* v_unused_4244_; 
v_unused_4244_ = lean_ctor_get(v___x_4236_, 0);
lean_dec(v_unused_4244_);
v___x_4238_ = v___x_4236_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_dec(v___x_4236_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
lean_ctor_set(v___x_4238_, 0, v___x_4235_);
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4235_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
else
{
return v___x_4236_;
}
}
}
}
else
{
lean_dec_ref(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v___x_4221_);
lean_dec(v_numNested_4213_);
lean_dec(v_all_4212_);
lean_dec(v_numParams_4211_);
lean_dec(v_indName_3995_);
return v___x_4224_;
}
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
lean_dec(v_numNested_4213_);
lean_dec(v_all_4212_);
lean_dec(v_numParams_4211_);
lean_dec(v_indName_3995_);
v___x_4247_ = lean_box(0);
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___x_4247_);
v___x_4249_ = v___x_4218_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_numNested_4213_);
lean_dec(v_all_4212_);
lean_dec(v_numParams_4211_);
lean_dec(v_indName_3995_);
v_a_4252_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4215_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4215_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4262_; 
lean_dec(v_a_4200_);
lean_dec(v_indName_3995_);
v___x_4260_ = lean_box(0);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4260_);
v___x_4262_ = v___x_4202_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
else
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
lean_dec(v_indName_3995_);
v_a_4265_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4199_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4199_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
goto v___jp_4132_;
}
}
else
{
goto v___jp_4132_;
}
v___jp_4085_:
{
lean_object* v___x_4089_; double v___x_4090_; double v___x_4091_; double v___x_4092_; double v___x_4093_; double v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4089_ = lean_io_mono_nanos_now();
v___x_4090_ = lean_float_of_nat(v___y_4086_);
v___x_4091_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4092_ = lean_float_div(v___x_4090_, v___x_4091_);
v___x_4093_ = lean_float_of_nat(v___x_4089_);
v___x_4094_ = lean_float_div(v___x_4093_, v___x_4091_);
v___x_4095_ = lean_box_float(v___x_4092_);
v___x_4096_ = lean_box_float(v___x_4094_);
v___x_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4098_, 0, v_a_4088_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4081_, v_hasTrace_4004_, v___x_4082_, v_options_4002_, v___x_4084_, v___y_4087_, v___f_4080_, v___x_4098_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4099_;
}
v___jp_4100_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_a_4103_);
v___y_4086_ = v___y_4101_;
v___y_4087_ = v___y_4102_;
v_a_4088_ = v___x_4104_;
goto v___jp_4085_;
}
v___jp_4105_:
{
lean_object* v___x_4109_; 
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_a_4108_);
v___y_4086_ = v___y_4106_;
v___y_4087_ = v___y_4107_;
v_a_4088_ = v___x_4109_;
goto v___jp_4085_;
}
v___jp_4110_:
{
lean_object* v___x_4114_; double v___x_4115_; double v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4114_ = lean_io_get_num_heartbeats();
v___x_4115_ = lean_float_of_nat(v___y_4112_);
v___x_4116_ = lean_float_of_nat(v___x_4114_);
v___x_4117_ = lean_box_float(v___x_4115_);
v___x_4118_ = lean_box_float(v___x_4116_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4117_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4120_, 0, v_a_4113_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4081_, v_hasTrace_4004_, v___x_4082_, v_options_4002_, v___x_4084_, v___y_4111_, v___f_4080_, v___x_4120_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4121_;
}
v___jp_4122_:
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_a_4125_);
v___y_4111_ = v___y_4123_;
v___y_4112_ = v___y_4124_;
v_a_4113_ = v___x_4126_;
goto v___jp_4110_;
}
v___jp_4127_:
{
lean_object* v___x_4131_; 
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_a_4130_);
v___y_4111_ = v___y_4128_;
v___y_4112_ = v___y_4129_;
v_a_4113_ = v___x_4131_;
goto v___jp_4110_;
}
v___jp_4132_:
{
lean_object* v___x_4133_; lean_object* v_a_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v___x_4133_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3999_);
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref(v___x_4133_);
v___x_4135_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4136_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4002_, v___x_4135_);
if (v___x_4136_ == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3995_);
v___x_4138_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
if (lean_obj_tag(v_a_4139_) == 5)
{
lean_object* v_val_4140_; uint8_t v_isRec_4141_; 
v_val_4140_ = lean_ctor_get(v_a_4139_, 0);
lean_inc_ref(v_val_4140_);
lean_dec_ref_known(v_a_4139_, 1);
v_isRec_4141_ = lean_ctor_get_uint8(v_val_4140_, sizeof(void*)*6);
if (v_isRec_4141_ == 0)
{
lean_object* v___x_4142_; 
lean_dec_ref(v_val_4140_);
lean_dec(v_indName_3995_);
v___x_4142_ = lean_box(0);
v___y_4101_ = v___x_4137_;
v___y_4102_ = v_a_4134_;
v_a_4103_ = v___x_4142_;
goto v___jp_4100_;
}
else
{
lean_object* v_toConstantVal_4143_; lean_object* v_numParams_4144_; lean_object* v_all_4145_; lean_object* v_numNested_4146_; lean_object* v_type_4147_; lean_object* v___x_4148_; 
v_toConstantVal_4143_ = lean_ctor_get(v_val_4140_, 0);
lean_inc_ref(v_toConstantVal_4143_);
v_numParams_4144_ = lean_ctor_get(v_val_4140_, 1);
lean_inc(v_numParams_4144_);
v_all_4145_ = lean_ctor_get(v_val_4140_, 3);
lean_inc(v_all_4145_);
v_numNested_4146_ = lean_ctor_get(v_val_4140_, 5);
lean_inc(v_numNested_4146_);
lean_dec_ref(v_val_4140_);
v_type_4147_ = lean_ctor_get(v_toConstantVal_4143_, 2);
lean_inc_ref(v_type_4147_);
lean_dec_ref(v_toConstantVal_4143_);
v___x_4148_ = l_Lean_Meta_isPropFormerType(v_type_4147_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; uint8_t v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = lean_unbox(v_a_4149_);
lean_dec(v_a_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_inc_n(v_indName_3995_, 2);
v___x_4151_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4152_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4145_);
v___x_4153_ = lean_array_mk(v_all_4145_);
lean_inc(v___x_4152_);
lean_inc_ref(v___x_4153_);
lean_inc(v_numParams_4144_);
lean_inc(v___x_4151_);
v___x_4154_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4151_, v_numParams_4144_, v___x_4153_, v___x_4152_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
lean_dec_ref_known(v___x_4154_, 1);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = l_List_get_x21Internal___redArg(v___x_4005_, v_all_4145_, v___x_4155_);
lean_dec(v_all_4145_);
v___x_4157_ = lean_name_eq(v___x_4156_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; 
lean_dec_ref(v___x_4153_);
lean_dec(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v_numNested_4146_);
lean_dec(v_numParams_4144_);
v___x_4158_ = lean_box(0);
v___y_4101_ = v___x_4137_;
v___y_4102_ = v_a_4134_;
v_a_4103_ = v___x_4158_;
goto v___jp_4100_;
}
else
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = lean_box(0);
v___x_4160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4146_, v___x_4151_, v___x_4152_, v_numParams_4144_, v___x_4153_, v___x_4155_, v___x_4159_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4146_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_dec_ref_known(v___x_4160_, 1);
v___y_4101_ = v___x_4137_;
v___y_4102_ = v_a_4134_;
v_a_4103_ = v___x_4159_;
goto v___jp_4100_;
}
else
{
lean_object* v_a_4161_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___y_4106_ = v___x_4137_;
v___y_4107_ = v_a_4134_;
v_a_4108_ = v_a_4161_;
goto v___jp_4105_;
}
}
}
else
{
lean_object* v_a_4162_; 
lean_dec_ref(v___x_4153_);
lean_dec(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v_numNested_4146_);
lean_dec(v_all_4145_);
lean_dec(v_numParams_4144_);
lean_dec(v_indName_3995_);
v_a_4162_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4154_, 1);
v___y_4106_ = v___x_4137_;
v___y_4107_ = v_a_4134_;
v_a_4108_ = v_a_4162_;
goto v___jp_4105_;
}
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_numNested_4146_);
lean_dec(v_all_4145_);
lean_dec(v_numParams_4144_);
lean_dec(v_indName_3995_);
v___x_4163_ = lean_box(0);
v___y_4101_ = v___x_4137_;
v___y_4102_ = v_a_4134_;
v_a_4103_ = v___x_4163_;
goto v___jp_4100_;
}
}
else
{
lean_object* v_a_4164_; 
lean_dec(v_numNested_4146_);
lean_dec(v_all_4145_);
lean_dec(v_numParams_4144_);
lean_dec(v_indName_3995_);
v_a_4164_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4148_, 1);
v___y_4106_ = v___x_4137_;
v___y_4107_ = v_a_4134_;
v_a_4108_ = v_a_4164_;
goto v___jp_4105_;
}
}
}
else
{
lean_object* v___x_4165_; 
lean_dec(v_a_4139_);
lean_dec(v_indName_3995_);
v___x_4165_ = lean_box(0);
v___y_4101_ = v___x_4137_;
v___y_4102_ = v_a_4134_;
v_a_4103_ = v___x_4165_;
goto v___jp_4100_;
}
}
else
{
lean_object* v_a_4166_; 
lean_dec(v_indName_3995_);
v_a_4166_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4138_, 1);
v___y_4106_ = v___x_4137_;
v___y_4107_ = v_a_4134_;
v_a_4108_ = v_a_4166_;
goto v___jp_4105_;
}
}
else
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3995_);
v___x_4168_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
if (lean_obj_tag(v_a_4169_) == 5)
{
lean_object* v_val_4170_; uint8_t v_isRec_4171_; 
v_val_4170_ = lean_ctor_get(v_a_4169_, 0);
lean_inc_ref(v_val_4170_);
lean_dec_ref_known(v_a_4169_, 1);
v_isRec_4171_ = lean_ctor_get_uint8(v_val_4170_, sizeof(void*)*6);
if (v_isRec_4171_ == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v_val_4170_);
lean_dec(v_indName_3995_);
v___x_4172_ = lean_box(0);
v___y_4123_ = v_a_4134_;
v___y_4124_ = v___x_4167_;
v_a_4125_ = v___x_4172_;
goto v___jp_4122_;
}
else
{
lean_object* v_toConstantVal_4173_; lean_object* v_numParams_4174_; lean_object* v_all_4175_; lean_object* v_numNested_4176_; lean_object* v_type_4177_; lean_object* v___x_4178_; 
v_toConstantVal_4173_ = lean_ctor_get(v_val_4170_, 0);
lean_inc_ref(v_toConstantVal_4173_);
v_numParams_4174_ = lean_ctor_get(v_val_4170_, 1);
lean_inc(v_numParams_4174_);
v_all_4175_ = lean_ctor_get(v_val_4170_, 3);
lean_inc(v_all_4175_);
v_numNested_4176_ = lean_ctor_get(v_val_4170_, 5);
lean_inc(v_numNested_4176_);
lean_dec_ref(v_val_4170_);
v_type_4177_ = lean_ctor_get(v_toConstantVal_4173_, 2);
lean_inc_ref(v_type_4177_);
lean_dec_ref(v_toConstantVal_4173_);
v___x_4178_ = l_Lean_Meta_isPropFormerType(v_type_4177_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; uint8_t v___x_4180_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = lean_unbox(v_a_4179_);
lean_dec(v_a_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_inc_n(v_indName_3995_, 2);
v___x_4181_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4182_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4175_);
v___x_4183_ = lean_array_mk(v_all_4175_);
lean_inc(v___x_4182_);
lean_inc_ref(v___x_4183_);
lean_inc(v_numParams_4174_);
lean_inc(v___x_4181_);
v___x_4184_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4181_, v_numParams_4174_, v___x_4183_, v___x_4182_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v___x_4185_; lean_object* v___x_4186_; uint8_t v___x_4187_; 
lean_dec_ref_known(v___x_4184_, 1);
v___x_4185_ = lean_unsigned_to_nat(0u);
v___x_4186_ = l_List_get_x21Internal___redArg(v___x_4005_, v_all_4175_, v___x_4185_);
lean_dec(v_all_4175_);
v___x_4187_ = lean_name_eq(v___x_4186_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; 
lean_dec_ref(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec(v___x_4181_);
lean_dec(v_numNested_4176_);
lean_dec(v_numParams_4174_);
v___x_4188_ = lean_box(0);
v___y_4123_ = v_a_4134_;
v___y_4124_ = v___x_4167_;
v_a_4125_ = v___x_4188_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_box(0);
v___x_4190_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4176_, v___x_4181_, v___x_4182_, v_numParams_4174_, v___x_4183_, v___x_4185_, v___x_4189_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4176_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_dec_ref_known(v___x_4190_, 1);
v___y_4123_ = v_a_4134_;
v___y_4124_ = v___x_4167_;
v_a_4125_ = v___x_4189_;
goto v___jp_4122_;
}
else
{
lean_object* v_a_4191_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4190_, 1);
v___y_4128_ = v_a_4134_;
v___y_4129_ = v___x_4167_;
v_a_4130_ = v_a_4191_;
goto v___jp_4127_;
}
}
}
else
{
lean_object* v_a_4192_; 
lean_dec_ref(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec(v___x_4181_);
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
v_a_4192_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4128_ = v_a_4134_;
v___y_4129_ = v___x_4167_;
v_a_4130_ = v_a_4192_;
goto v___jp_4127_;
}
}
else
{
lean_object* v___x_4193_; 
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
v___x_4193_ = lean_box(0);
v___y_4123_ = v_a_4134_;
v___y_4124_ = v___x_4167_;
v_a_4125_ = v___x_4193_;
goto v___jp_4122_;
}
}
else
{
lean_object* v_a_4194_; 
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
v_a_4194_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4194_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4128_ = v_a_4134_;
v___y_4129_ = v___x_4167_;
v_a_4130_ = v_a_4194_;
goto v___jp_4127_;
}
}
}
else
{
lean_object* v___x_4195_; 
lean_dec(v_a_4169_);
lean_dec(v_indName_3995_);
v___x_4195_ = lean_box(0);
v___y_4123_ = v_a_4134_;
v___y_4124_ = v___x_4167_;
v_a_4125_ = v___x_4195_;
goto v___jp_4122_;
}
}
else
{
lean_object* v_a_4196_; 
lean_dec(v_indName_3995_);
v_a_4196_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_4128_ = v_a_4134_;
v___y_4129_ = v___x_4167_;
v_a_4130_ = v_a_4196_;
goto v___jp_4127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_mkBRecOn(v_indName_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v_inst_4285_, lean_object* v_R_4286_, lean_object* v_a_4287_, lean_object* v_b_4288_, lean_object* v_c_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4280_, v___x_4281_, v___x_4282_, v___x_4283_, v___x_4284_, v_a_4287_, v_b_4288_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4296_, lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v_inst_4301_, lean_object* v_R_4302_, lean_object* v_a_4303_, lean_object* v_b_4304_, lean_object* v_c_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4296_, v___x_4297_, v___x_4298_, v___x_4299_, v___x_4300_, v_inst_4301_, v_R_4302_, v_a_4303_, v_b_4304_, v_c_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v_upperBound_4296_);
return v_res_4311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = lean_unsigned_to_nat(2304625798u);
v___x_4358_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4359_ = l_Lean_Name_num___override(v___x_4358_, v___x_4357_);
return v___x_4359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4362_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4363_ = l_Lean_Name_str___override(v___x_4362_, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4366_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4367_ = l_Lean_Name_str___override(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4368_ = lean_unsigned_to_nat(2u);
v___x_4369_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4370_ = l_Lean_Name_num___override(v___x_4369_, v___x_4368_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4372_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4373_ = 0;
v___x_4374_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4375_ = l_Lean_registerTraceClass(v___x_4372_, v___x_4373_, v___x_4374_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4377_;
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
