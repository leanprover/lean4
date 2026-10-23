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
lean_object* v___f_435_; lean_object* v___x_5002__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_5002__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_5002__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
uint8_t v___x_9141__boxed_554_; lean_object* v_res_555_; 
v___x_9141__boxed_554_ = lean_unbox(v___x_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_545_, v___x_9141__boxed_554_, v_targs_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
if (lean_obj_tag(v_a_810_) == 0)
{
lean_object* v___x_812_; 
v___x_812_ = l_List_reverse___redArg(v_a_811_);
return v___x_812_;
}
else
{
lean_object* v_head_813_; lean_object* v_tail_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_823_; 
v_head_813_ = lean_ctor_get(v_a_810_, 0);
v_tail_814_ = lean_ctor_get(v_a_810_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_823_ == 0)
{
v___x_816_ = v_a_810_;
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_tail_814_);
lean_inc(v_head_813_);
lean_dec(v_a_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_823_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = l_Lean_Level_param___override(v_head_813_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v_a_811_);
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_818_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_811_);
v___x_820_ = v_reuseFailAlloc_822_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v_a_810_ = v_tail_814_;
v_a_811_ = v___x_820_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_824_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_830_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_ctor_set(v___x_830_, 4, v___x_829_);
lean_ctor_set(v___x_830_, 5, v___x_829_);
lean_ctor_set(v___x_830_, 6, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_831_, uint8_t v_s_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_env_837_; lean_object* v_nextMacroScope_838_; lean_object* v_ngen_839_; lean_object* v_auxDeclNGen_840_; lean_object* v_traceState_841_; lean_object* v_recordedDeps_842_; lean_object* v_messages_843_; lean_object* v_infoState_844_; lean_object* v_snapshotTasks_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_874_; 
v___x_836_ = lean_st_ref_take(v___y_834_);
v_env_837_ = lean_ctor_get(v___x_836_, 0);
v_nextMacroScope_838_ = lean_ctor_get(v___x_836_, 1);
v_ngen_839_ = lean_ctor_get(v___x_836_, 2);
v_auxDeclNGen_840_ = lean_ctor_get(v___x_836_, 3);
v_traceState_841_ = lean_ctor_get(v___x_836_, 4);
v_recordedDeps_842_ = lean_ctor_get(v___x_836_, 6);
v_messages_843_ = lean_ctor_get(v___x_836_, 7);
v_infoState_844_ = lean_ctor_get(v___x_836_, 8);
v_snapshotTasks_845_ = lean_ctor_get(v___x_836_, 9);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_836_, 5);
lean_dec(v_unused_875_);
v___x_847_ = v___x_836_;
v_isShared_848_ = v_isSharedCheck_874_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snapshotTasks_845_);
lean_inc(v_infoState_844_);
lean_inc(v_messages_843_);
lean_inc(v_recordedDeps_842_);
lean_inc(v_traceState_841_);
lean_inc(v_auxDeclNGen_840_);
lean_inc(v_ngen_839_);
lean_inc(v_nextMacroScope_838_);
lean_inc(v_env_837_);
lean_dec(v___x_836_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_874_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_849_ = 0;
v___x_850_ = lean_box(0);
v___x_851_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_837_, v_declName_831_, v_s_832_, v___x_849_, v___x_850_);
v___x_852_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 5, v___x_852_);
lean_ctor_set(v___x_847_, 0, v___x_851_);
v___x_854_ = v___x_847_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_nextMacroScope_838_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_ngen_839_);
lean_ctor_set(v_reuseFailAlloc_873_, 3, v_auxDeclNGen_840_);
lean_ctor_set(v_reuseFailAlloc_873_, 4, v_traceState_841_);
lean_ctor_set(v_reuseFailAlloc_873_, 5, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_873_, 6, v_recordedDeps_842_);
lean_ctor_set(v_reuseFailAlloc_873_, 7, v_messages_843_);
lean_ctor_set(v_reuseFailAlloc_873_, 8, v_infoState_844_);
lean_ctor_set(v_reuseFailAlloc_873_, 9, v_snapshotTasks_845_);
v___x_854_ = v_reuseFailAlloc_873_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_mctx_857_; lean_object* v_zetaDeltaFVarIds_858_; lean_object* v_postponed_859_; lean_object* v_diag_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_871_; 
v___x_855_ = lean_st_ref_put(v___y_834_, v___x_854_);
v___x_856_ = lean_st_ref_take(v___y_833_);
v_mctx_857_ = lean_ctor_get(v___x_856_, 0);
v_zetaDeltaFVarIds_858_ = lean_ctor_get(v___x_856_, 2);
v_postponed_859_ = lean_ctor_get(v___x_856_, 3);
v_diag_860_ = lean_ctor_get(v___x_856_, 4);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_856_, 1);
lean_dec(v_unused_872_);
v___x_862_ = v___x_856_;
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_diag_860_);
lean_inc(v_postponed_859_);
lean_inc(v_zetaDeltaFVarIds_858_);
lean_inc(v_mctx_857_);
lean_dec(v___x_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_871_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_865_);
v___x_867_ = v___x_862_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_mctx_857_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_zetaDeltaFVarIds_858_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_postponed_859_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_diag_860_);
v___x_867_ = v_reuseFailAlloc_870_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_st_ref_put(v___y_833_, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_864_);
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_876_, lean_object* v_s_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v_s_boxed_881_; lean_object* v_res_882_; 
v_s_boxed_881_ = lean_unbox(v_s_877_);
v_res_882_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_876_, v_s_boxed_881_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_889_; lean_object* v___x_890_; 
v___x_889_ = 0;
v___x_890_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_883_, v___x_889_, v___y_885_, v___y_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_898_, lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_toCold_905_; lean_object* v_currRecDepth_906_; lean_object* v_ref_907_; uint16_t v_optionFlags_908_; uint8_t v_suppressElabErrors_909_; uint8_t v_checkDeprecated_910_; uint8_t v_isRecordingDeps_911_; lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_toCold_905_ = lean_ctor_get(v___y_902_, 0);
v_currRecDepth_906_ = lean_ctor_get(v___y_902_, 1);
v_ref_907_ = lean_ctor_get(v___y_902_, 2);
v_optionFlags_908_ = lean_ctor_get_uint16(v___y_902_, sizeof(void*)*3);
v_suppressElabErrors_909_ = lean_ctor_get_uint8(v___y_902_, sizeof(void*)*3 + 2);
v_checkDeprecated_910_ = lean_ctor_get_uint8(v___y_902_, sizeof(void*)*3 + 3);
v_isRecordingDeps_911_ = lean_ctor_get_uint8(v___y_902_, sizeof(void*)*3 + 4);
v_ref_912_ = l_Lean_replaceRef(v_ref_898_, v_ref_907_);
lean_inc(v_currRecDepth_906_);
lean_inc_ref(v_toCold_905_);
v___x_913_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_913_, 0, v_toCold_905_);
lean_ctor_set(v___x_913_, 1, v_currRecDepth_906_);
lean_ctor_set(v___x_913_, 2, v_ref_912_);
lean_ctor_set_uint16(v___x_913_, sizeof(void*)*3, v_optionFlags_908_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 2, v_suppressElabErrors_909_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 3, v_checkDeprecated_910_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 4, v_isRecordingDeps_911_);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_899_, v___y_900_, v___y_901_, v___x_913_, v___y_903_);
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
lean_inc_ref(v___x_973_);
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
v___x_982_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_973_, v_declHint_964_);
lean_dec_ref(v___x_973_);
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
lean_object* v___x_994_; lean_object* v_moduleNames_995_; lean_object* v_mod_996_; uint8_t v___x_997_; 
v___x_994_ = l_Lean_Environment_header(v_env_969_);
lean_dec_ref(v_env_969_);
v_moduleNames_995_ = lean_ctor_get(v___x_994_, 4);
lean_inc_ref(v_moduleNames_995_);
lean_dec_ref(v___x_994_);
v_mod_996_ = lean_array_get(v___x_967_, v_moduleNames_995_, v_val_990_);
lean_dec(v_val_990_);
lean_dec_ref(v_moduleNames_995_);
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
lean_object* v_toCold_1581_; lean_object* v_currRecDepth_1582_; lean_object* v_ref_1583_; uint16_t v_optionFlags_1584_; uint8_t v_suppressElabErrors_1585_; uint8_t v_checkDeprecated_1586_; uint8_t v_isRecordingDeps_1587_; lean_object* v_ref_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_traceState_1591_; lean_object* v_traces_1592_; lean_object* v___x_1593_; size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; lean_object* v_msg_1597_; lean_object* v___x_1598_; lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1637_; 
v_toCold_1581_ = lean_ctor_get(v___y_1578_, 0);
v_currRecDepth_1582_ = lean_ctor_get(v___y_1578_, 1);
v_ref_1583_ = lean_ctor_get(v___y_1578_, 2);
v_optionFlags_1584_ = lean_ctor_get_uint16(v___y_1578_, sizeof(void*)*3);
v_suppressElabErrors_1585_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 2);
v_checkDeprecated_1586_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1587_ = lean_ctor_get_uint8(v___y_1578_, sizeof(void*)*3 + 4);
v_ref_1588_ = l_Lean_replaceRef(v_ref_1574_, v_ref_1583_);
lean_inc(v_currRecDepth_1582_);
lean_inc_ref(v_toCold_1581_);
v___x_1589_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1589_, 0, v_toCold_1581_);
lean_ctor_set(v___x_1589_, 1, v_currRecDepth_1582_);
lean_ctor_set(v___x_1589_, 2, v_ref_1588_);
lean_ctor_set_uint16(v___x_1589_, sizeof(void*)*3, v_optionFlags_1584_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*3 + 2, v_suppressElabErrors_1585_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*3 + 3, v_checkDeprecated_1586_);
lean_ctor_set_uint8(v___x_1589_, sizeof(void*)*3 + 4, v_isRecordingDeps_1587_);
v___x_1590_ = lean_st_ref_get(v___y_1579_);
v_traceState_1591_ = lean_ctor_get(v___x_1590_, 4);
lean_inc_ref(v_traceState_1591_);
lean_dec(v___x_1590_);
v_traces_1592_ = lean_ctor_get(v_traceState_1591_, 0);
lean_inc_ref(v_traces_1592_);
lean_dec_ref(v_traceState_1591_);
v___x_1593_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1592_);
lean_dec_ref(v_traces_1592_);
v_sz_1594_ = lean_array_size(v___x_1593_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1594_, v___x_1595_, v___x_1593_);
v_msg_1597_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1597_, 0, v_data_1573_);
lean_ctor_set(v_msg_1597_, 1, v_msg_1575_);
lean_ctor_set(v_msg_1597_, 2, v___x_1596_);
v___x_1598_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1597_, v___y_1576_, v___y_1577_, v___x_1589_, v___y_1579_);
lean_dec_ref_known(v___x_1589_, 3);
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1637_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; lean_object* v_traceState_1604_; lean_object* v_env_1605_; lean_object* v_nextMacroScope_1606_; lean_object* v_ngen_1607_; lean_object* v_auxDeclNGen_1608_; lean_object* v_cache_1609_; lean_object* v_recordedDeps_1610_; lean_object* v_messages_1611_; lean_object* v_infoState_1612_; lean_object* v_snapshotTasks_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1636_; 
v___x_1603_ = lean_st_ref_take(v___y_1579_);
v_traceState_1604_ = lean_ctor_get(v___x_1603_, 4);
v_env_1605_ = lean_ctor_get(v___x_1603_, 0);
v_nextMacroScope_1606_ = lean_ctor_get(v___x_1603_, 1);
v_ngen_1607_ = lean_ctor_get(v___x_1603_, 2);
v_auxDeclNGen_1608_ = lean_ctor_get(v___x_1603_, 3);
v_cache_1609_ = lean_ctor_get(v___x_1603_, 5);
v_recordedDeps_1610_ = lean_ctor_get(v___x_1603_, 6);
v_messages_1611_ = lean_ctor_get(v___x_1603_, 7);
v_infoState_1612_ = lean_ctor_get(v___x_1603_, 8);
v_snapshotTasks_1613_ = lean_ctor_get(v___x_1603_, 9);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1615_ = v___x_1603_;
v_isShared_1616_ = v_isSharedCheck_1636_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_snapshotTasks_1613_);
lean_inc(v_infoState_1612_);
lean_inc(v_messages_1611_);
lean_inc(v_recordedDeps_1610_);
lean_inc(v_cache_1609_);
lean_inc(v_traceState_1604_);
lean_inc(v_auxDeclNGen_1608_);
lean_inc(v_ngen_1607_);
lean_inc(v_nextMacroScope_1606_);
lean_inc(v_env_1605_);
lean_dec(v___x_1603_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1636_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
uint64_t v_tid_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1634_; 
v_tid_1617_ = lean_ctor_get_uint64(v_traceState_1604_, sizeof(void*)*1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v_traceState_1604_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v_traceState_1604_, 0);
lean_dec(v_unused_1635_);
v___x_1619_ = v_traceState_1604_;
v_isShared_1620_ = v_isSharedCheck_1634_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_traceState_1604_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1634_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_ref_1574_);
lean_ctor_set(v___x_1622_, 1, v_a_1599_);
v___x_1623_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1572_, v___x_1622_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1623_);
v___x_1625_ = v___x_1619_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1623_);
lean_ctor_set_uint64(v_reuseFailAlloc_1633_, sizeof(void*)*1, v_tid_1617_);
v___x_1625_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 4, v___x_1625_);
v___x_1627_ = v___x_1615_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_env_1605_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_nextMacroScope_1606_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_ngen_1607_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_auxDeclNGen_1608_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1632_, 5, v_cache_1609_);
lean_ctor_set(v_reuseFailAlloc_1632_, 6, v_recordedDeps_1610_);
lean_ctor_set(v_reuseFailAlloc_1632_, 7, v_messages_1611_);
lean_ctor_set(v_reuseFailAlloc_1632_, 8, v_infoState_1612_);
lean_ctor_set(v_reuseFailAlloc_1632_, 9, v_snapshotTasks_1613_);
v___x_1627_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_st_ref_put(v___y_1579_, v___x_1627_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1621_);
v___x_1630_ = v___x_1601_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1621_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1638_, lean_object* v_data_1639_, lean_object* v_ref_1640_, lean_object* v_msg_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1638_, v_data_1639_, v_ref_1640_, v_msg_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1647_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1648_; double v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_float_of_nat(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1653_; double v___x_1654_; 
v___x_1653_ = lean_unsigned_to_nat(1000u);
v___x_1654_ = lean_float_of_nat(v___x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1655_, uint8_t v_collapsed_1656_, lean_object* v_tag_1657_, lean_object* v_opts_1658_, uint8_t v_clsEnabled_1659_, lean_object* v_oldTraces_1660_, lean_object* v_msg_1661_, lean_object* v_resStartStop_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_fst_1668_; lean_object* v_snd_1669_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v_data_1673_; lean_object* v_fst_1676_; lean_object* v_snd_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___y_1681_; lean_object* v_a_1682_; uint8_t v___y_1697_; double v___y_1729_; 
v_fst_1668_ = lean_ctor_get(v_resStartStop_1662_, 0);
lean_inc(v_fst_1668_);
v_snd_1669_ = lean_ctor_get(v_resStartStop_1662_, 1);
lean_inc(v_snd_1669_);
lean_dec_ref(v_resStartStop_1662_);
v_fst_1676_ = lean_ctor_get(v_snd_1669_, 0);
lean_inc(v_fst_1676_);
v_snd_1677_ = lean_ctor_get(v_snd_1669_, 1);
lean_inc(v_snd_1677_);
lean_dec(v_snd_1669_);
v___x_1678_ = l_Lean_trace_profiler;
v___x_1679_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1658_, v___x_1678_);
if (v___x_1679_ == 0)
{
v___y_1697_ = v___x_1679_;
goto v___jp_1696_;
}
else
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1735_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1658_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; double v___x_1738_; double v___x_1739_; double v___x_1740_; 
v___x_1736_ = l_Lean_trace_profiler_threshold;
v___x_1737_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1658_, v___x_1736_);
v___x_1738_ = lean_float_of_nat(v___x_1737_);
v___x_1739_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1740_ = lean_float_div(v___x_1738_, v___x_1739_);
v___y_1729_ = v___x_1740_;
goto v___jp_1728_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; double v___x_1743_; 
v___x_1741_ = l_Lean_trace_profiler_threshold;
v___x_1742_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1658_, v___x_1741_);
v___x_1743_ = lean_float_of_nat(v___x_1742_);
v___y_1729_ = v___x_1743_;
goto v___jp_1728_;
}
}
v___jp_1670_:
{
lean_object* v___x_1674_; 
lean_inc(v___y_1671_);
v___x_1674_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1660_, v_data_1673_, v___y_1671_, v___y_1672_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v___x_1675_; 
lean_dec_ref_known(v___x_1674_, 1);
v___x_1675_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1668_);
return v___x_1675_;
}
else
{
lean_dec(v_fst_1668_);
return v___x_1674_;
}
}
v___jp_1680_:
{
uint8_t v_result_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; double v___x_1686_; lean_object* v_data_1687_; 
v_result_1683_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1668_);
v___x_1684_ = lean_box(v_result_1683_);
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___x_1686_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1657_);
lean_inc_ref(v___x_1685_);
lean_inc(v_cls_1655_);
v_data_1687_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1687_, 0, v_cls_1655_);
lean_ctor_set(v_data_1687_, 1, v___x_1685_);
lean_ctor_set(v_data_1687_, 2, v_tag_1657_);
lean_ctor_set_float(v_data_1687_, sizeof(void*)*3, v___x_1686_);
lean_ctor_set_float(v_data_1687_, sizeof(void*)*3 + 8, v___x_1686_);
lean_ctor_set_uint8(v_data_1687_, sizeof(void*)*3 + 16, v_collapsed_1656_);
if (v___x_1679_ == 0)
{
lean_dec_ref_known(v___x_1685_, 1);
lean_dec(v_snd_1677_);
lean_dec(v_fst_1676_);
lean_dec_ref(v_tag_1657_);
lean_dec(v_cls_1655_);
v___y_1671_ = v___y_1681_;
v___y_1672_ = v_a_1682_;
v_data_1673_ = v_data_1687_;
goto v___jp_1670_;
}
else
{
lean_object* v_data_1688_; double v___x_1689_; double v___x_1690_; 
lean_dec_ref_known(v_data_1687_, 3);
v_data_1688_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1688_, 0, v_cls_1655_);
lean_ctor_set(v_data_1688_, 1, v___x_1685_);
lean_ctor_set(v_data_1688_, 2, v_tag_1657_);
v___x_1689_ = lean_unbox_float(v_fst_1676_);
lean_dec(v_fst_1676_);
lean_ctor_set_float(v_data_1688_, sizeof(void*)*3, v___x_1689_);
v___x_1690_ = lean_unbox_float(v_snd_1677_);
lean_dec(v_snd_1677_);
lean_ctor_set_float(v_data_1688_, sizeof(void*)*3 + 8, v___x_1690_);
lean_ctor_set_uint8(v_data_1688_, sizeof(void*)*3 + 16, v_collapsed_1656_);
v___y_1671_ = v___y_1681_;
v___y_1672_ = v_a_1682_;
v_data_1673_ = v_data_1688_;
goto v___jp_1670_;
}
}
v___jp_1691_:
{
lean_object* v_ref_1692_; lean_object* v___x_1693_; 
v_ref_1692_ = lean_ctor_get(v___y_1665_, 2);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v_fst_1668_);
v___x_1693_ = lean_apply_6(v_msg_1661_, v_fst_1668_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, lean_box(0));
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___y_1681_ = v_ref_1692_;
v_a_1682_ = v_a_1694_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1695_; 
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1681_ = v_ref_1692_;
v_a_1682_ = v___x_1695_;
goto v___jp_1680_;
}
}
v___jp_1696_:
{
if (v_clsEnabled_1659_ == 0)
{
if (v___y_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v_traceState_1699_; lean_object* v_env_1700_; lean_object* v_nextMacroScope_1701_; lean_object* v_ngen_1702_; lean_object* v_auxDeclNGen_1703_; lean_object* v_cache_1704_; lean_object* v_recordedDeps_1705_; lean_object* v_messages_1706_; lean_object* v_infoState_1707_; lean_object* v_snapshotTasks_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_snd_1677_);
lean_dec(v_fst_1676_);
lean_dec_ref(v_msg_1661_);
lean_dec_ref(v_tag_1657_);
lean_dec(v_cls_1655_);
v___x_1698_ = lean_st_ref_take(v___y_1666_);
v_traceState_1699_ = lean_ctor_get(v___x_1698_, 4);
v_env_1700_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1701_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1702_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1703_ = lean_ctor_get(v___x_1698_, 3);
v_cache_1704_ = lean_ctor_get(v___x_1698_, 5);
v_recordedDeps_1705_ = lean_ctor_get(v___x_1698_, 6);
v_messages_1706_ = lean_ctor_get(v___x_1698_, 7);
v_infoState_1707_ = lean_ctor_get(v___x_1698_, 8);
v_snapshotTasks_1708_ = lean_ctor_get(v___x_1698_, 9);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1710_ = v___x_1698_;
v_isShared_1711_ = v_isSharedCheck_1727_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snapshotTasks_1708_);
lean_inc(v_infoState_1707_);
lean_inc(v_messages_1706_);
lean_inc(v_recordedDeps_1705_);
lean_inc(v_cache_1704_);
lean_inc(v_traceState_1699_);
lean_inc(v_auxDeclNGen_1703_);
lean_inc(v_ngen_1702_);
lean_inc(v_nextMacroScope_1701_);
lean_inc(v_env_1700_);
lean_dec(v___x_1698_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1727_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
uint64_t v_tid_1712_; lean_object* v_traces_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1726_; 
v_tid_1712_ = lean_ctor_get_uint64(v_traceState_1699_, sizeof(void*)*1);
v_traces_1713_ = lean_ctor_get(v_traceState_1699_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_traceState_1699_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1715_ = v_traceState_1699_;
v_isShared_1716_ = v_isSharedCheck_1726_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_traces_1713_);
lean_dec(v_traceState_1699_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1726_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1660_, v_traces_1713_);
lean_dec_ref(v_traces_1713_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1717_);
lean_ctor_set_uint64(v_reuseFailAlloc_1725_, sizeof(void*)*1, v_tid_1712_);
v___x_1719_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 4, v___x_1719_);
v___x_1721_ = v___x_1710_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_env_1700_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_nextMacroScope_1701_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_ngen_1702_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_auxDeclNGen_1703_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_cache_1704_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_recordedDeps_1705_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_messages_1706_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_infoState_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_snapshotTasks_1708_);
v___x_1721_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_st_ref_put(v___y_1666_, v___x_1721_);
v___x_1723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1668_);
return v___x_1723_;
}
}
}
}
}
else
{
goto v___jp_1691_;
}
}
else
{
goto v___jp_1691_;
}
}
v___jp_1728_:
{
double v___x_1730_; double v___x_1731_; double v___x_1732_; uint8_t v___x_1733_; 
v___x_1730_ = lean_unbox_float(v_snd_1677_);
v___x_1731_ = lean_unbox_float(v_fst_1676_);
v___x_1732_ = lean_float_sub(v___x_1730_, v___x_1731_);
v___x_1733_ = lean_float_decLt(v___y_1729_, v___x_1732_);
v___y_1697_ = v___x_1733_;
goto v___jp_1696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1744_, lean_object* v_collapsed_1745_, lean_object* v_tag_1746_, lean_object* v_opts_1747_, lean_object* v_clsEnabled_1748_, lean_object* v_oldTraces_1749_, lean_object* v_msg_1750_, lean_object* v_resStartStop_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
uint8_t v_collapsed_boxed_1757_; uint8_t v_clsEnabled_boxed_1758_; lean_object* v_res_1759_; 
v_collapsed_boxed_1757_ = lean_unbox(v_collapsed_1745_);
v_clsEnabled_boxed_1758_ = lean_unbox(v_clsEnabled_1748_);
v_res_1759_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1744_, v_collapsed_boxed_1757_, v_tag_1746_, v_opts_1747_, v_clsEnabled_boxed_1758_, v_oldTraces_1749_, v_msg_1750_, v_resStartStop_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec_ref(v_opts_1747_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1760_, lean_object* v___x_1761_, lean_object* v___x_1762_, lean_object* v___x_1763_, lean_object* v_a_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
uint8_t v___x_1771_; 
v___x_1771_ = lean_nat_dec_lt(v_a_1764_, v_upperBound_1760_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec(v_a_1764_);
lean_dec(v___x_1763_);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_b_1765_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_a_1764_, v___x_1774_);
lean_dec(v_a_1764_);
lean_inc_n(v___x_1775_, 2);
lean_inc(v___x_1761_);
v___x_1776_ = lean_name_append_index_after(v___x_1761_, v___x_1775_);
lean_inc(v___x_1762_);
v___x_1777_ = lean_name_append_index_after(v___x_1762_, v___x_1775_);
lean_inc(v___x_1763_);
v___x_1778_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1776_, v___x_1763_, v___x_1777_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_dec_ref_known(v___x_1778_, 1);
v_a_1764_ = v___x_1775_;
v_b_1765_ = v___x_1773_;
goto _start;
}
else
{
lean_dec(v___x_1775_);
lean_dec(v___x_1763_);
lean_dec(v___x_1762_);
lean_dec(v___x_1761_);
return v___x_1778_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v___x_1783_, lean_object* v_a_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1780_, v___x_1781_, v___x_1782_, v___x_1783_, v_a_1784_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v_upperBound_1780_);
return v_res_1791_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1802_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1803_ = l_Lean_Name_append(v___x_1802_, v___x_1801_);
return v___x_1803_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1804_; double v___x_1805_; 
v___x_1804_ = lean_unsigned_to_nat(1000000000u);
v___x_1805_ = lean_float_of_nat(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_toCold_1812_; lean_object* v_options_1813_; lean_object* v_inheritedTraceOptions_1814_; uint8_t v_hasTrace_1815_; lean_object* v___x_1816_; 
v_toCold_1812_ = lean_ctor_get(v_a_1809_, 0);
v_options_1813_ = lean_ctor_get(v_toCold_1812_, 2);
v_inheritedTraceOptions_1814_ = lean_ctor_get(v_toCold_1812_, 11);
v_hasTrace_1815_ = lean_ctor_get_uint8(v_options_1813_, sizeof(void*)*1);
v___x_1816_ = lean_box(0);
if (v_hasTrace_1815_ == 0)
{
lean_object* v___x_1817_; 
lean_inc(v_indName_1806_);
v___x_1817_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1881_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1881_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1881_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
if (lean_obj_tag(v_a_1818_) == 5)
{
lean_object* v_val_1822_; uint8_t v_isRec_1823_; 
v_val_1822_ = lean_ctor_get(v_a_1818_, 0);
lean_inc_ref(v_val_1822_);
lean_dec_ref_known(v_a_1818_, 1);
v_isRec_1823_ = lean_ctor_get_uint8(v_val_1822_, sizeof(void*)*6);
if (v_isRec_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
lean_dec_ref(v_val_1822_);
lean_dec(v_indName_1806_);
v___x_1824_ = lean_box(0);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1824_);
v___x_1826_ = v___x_1820_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
else
{
lean_object* v_toConstantVal_1828_; lean_object* v_numParams_1829_; lean_object* v_all_1830_; lean_object* v_numNested_1831_; lean_object* v_type_1832_; lean_object* v___x_1833_; 
lean_del_object(v___x_1820_);
v_toConstantVal_1828_ = lean_ctor_get(v_val_1822_, 0);
lean_inc_ref(v_toConstantVal_1828_);
v_numParams_1829_ = lean_ctor_get(v_val_1822_, 1);
lean_inc(v_numParams_1829_);
v_all_1830_ = lean_ctor_get(v_val_1822_, 3);
lean_inc(v_all_1830_);
v_numNested_1831_ = lean_ctor_get(v_val_1822_, 5);
lean_inc(v_numNested_1831_);
lean_dec_ref(v_val_1822_);
v_type_1832_ = lean_ctor_get(v_toConstantVal_1828_, 2);
lean_inc_ref(v_type_1832_);
lean_dec_ref(v_toConstantVal_1828_);
v___x_1833_ = l_Lean_Meta_isPropFormerType(v_type_1832_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1868_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1868_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1868_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_unbox(v_a_1834_);
lean_dec(v_a_1834_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1836_);
lean_inc_n(v_indName_1806_, 2);
v___x_1839_ = l_Lean_mkRecName(v_indName_1806_);
v___x_1840_ = l_Lean_mkBelowName(v_indName_1806_);
lean_inc(v___x_1840_);
lean_inc(v_numParams_1829_);
lean_inc(v___x_1839_);
v___x_1841_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1839_, v_numParams_1829_, v___x_1840_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1862_; 
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1863_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1862_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1862_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = l_List_get_x21Internal___redArg(v___x_1816_, v_all_1830_, v___x_1845_);
lean_dec(v_all_1830_);
v___x_1847_ = lean_name_eq(v___x_1846_, v_indName_1806_);
lean_dec(v_indName_1806_);
lean_dec(v___x_1846_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec(v___x_1840_);
lean_dec(v___x_1839_);
lean_dec(v_numNested_1831_);
lean_dec(v_numParams_1829_);
v___x_1848_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1848_);
v___x_1850_ = v___x_1843_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_del_object(v___x_1843_);
v___x_1852_ = lean_box(0);
v___x_1853_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1831_, v___x_1839_, v___x_1840_, v_numParams_1829_, v___x_1845_, v___x_1852_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_numNested_1831_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1853_, 0);
lean_dec(v_unused_1861_);
v___x_1855_ = v___x_1853_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v___x_1853_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1852_);
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1852_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
return v___x_1853_;
}
}
}
}
else
{
lean_dec(v___x_1840_);
lean_dec(v___x_1839_);
lean_dec(v_numNested_1831_);
lean_dec(v_all_1830_);
lean_dec(v_numParams_1829_);
lean_dec(v_indName_1806_);
return v___x_1841_;
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_numNested_1831_);
lean_dec(v_all_1830_);
lean_dec(v_numParams_1829_);
lean_dec(v_indName_1806_);
v___x_1864_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1864_);
v___x_1866_ = v___x_1836_;
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
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_numNested_1831_);
lean_dec(v_all_1830_);
lean_dec(v_numParams_1829_);
lean_dec(v_indName_1806_);
v_a_1869_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1833_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1833_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec(v_a_1818_);
lean_dec(v_indName_1806_);
v___x_1877_ = lean_box(0);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1877_);
v___x_1879_ = v___x_1820_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_indName_1806_);
v_a_1882_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1817_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1817_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v___f_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_a_1898_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v_a_1913_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v_a_1918_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_a_1923_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v_a_1935_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_a_1940_; 
lean_inc(v_indName_1806_);
v___f_1890_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1890_, 0, v_indName_1806_);
v___x_1891_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1892_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1893_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1894_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1814_, v_options_1813_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = l_Lean_trace_profiler;
v___x_2006_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1813_, v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; 
lean_dec_ref(v___f_1890_);
lean_inc(v_indName_1806_);
v___x_2007_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2071_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2071_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2071_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 5)
{
lean_object* v_val_2012_; uint8_t v_isRec_2013_; 
v_val_2012_ = lean_ctor_get(v_a_2008_, 0);
lean_inc_ref(v_val_2012_);
lean_dec_ref_known(v_a_2008_, 1);
v_isRec_2013_ = lean_ctor_get_uint8(v_val_2012_, sizeof(void*)*6);
if (v_isRec_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2016_; 
lean_dec_ref(v_val_2012_);
lean_dec(v_indName_1806_);
v___x_2014_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
lean_object* v_toConstantVal_2018_; lean_object* v_numParams_2019_; lean_object* v_all_2020_; lean_object* v_numNested_2021_; lean_object* v_type_2022_; lean_object* v___x_2023_; 
lean_del_object(v___x_2010_);
v_toConstantVal_2018_ = lean_ctor_get(v_val_2012_, 0);
lean_inc_ref(v_toConstantVal_2018_);
v_numParams_2019_ = lean_ctor_get(v_val_2012_, 1);
lean_inc(v_numParams_2019_);
v_all_2020_ = lean_ctor_get(v_val_2012_, 3);
lean_inc(v_all_2020_);
v_numNested_2021_ = lean_ctor_get(v_val_2012_, 5);
lean_inc(v_numNested_2021_);
lean_dec_ref(v_val_2012_);
v_type_2022_ = lean_ctor_get(v_toConstantVal_2018_, 2);
lean_inc_ref(v_type_2022_);
lean_dec_ref(v_toConstantVal_2018_);
v___x_2023_ = l_Lean_Meta_isPropFormerType(v_type_2022_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2058_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2058_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2058_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_unbox(v_a_2024_);
lean_dec(v_a_2024_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_del_object(v___x_2026_);
lean_inc_n(v_indName_1806_, 2);
v___x_2029_ = l_Lean_mkRecName(v_indName_1806_);
v___x_2030_ = l_Lean_mkBelowName(v_indName_1806_);
lean_inc(v___x_2030_);
lean_inc(v_numParams_2019_);
lean_inc(v___x_2029_);
v___x_2031_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2029_, v_numParams_2019_, v___x_2030_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2052_; 
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2053_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2052_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = l_List_get_x21Internal___redArg(v___x_1816_, v_all_2020_, v___x_2035_);
lean_dec(v_all_2020_);
v___x_2037_ = lean_name_eq(v___x_2036_, v_indName_1806_);
lean_dec(v_indName_1806_);
lean_dec(v___x_2036_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec(v___x_2030_);
lean_dec(v___x_2029_);
lean_dec(v_numNested_2021_);
lean_dec(v_numParams_2019_);
v___x_2038_ = lean_box(0);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2038_);
v___x_2040_ = v___x_2033_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_del_object(v___x_2033_);
v___x_2042_ = lean_box(0);
v___x_2043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2021_, v___x_2029_, v___x_2030_, v_numParams_2019_, v___x_2035_, v___x_2042_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_numNested_2021_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2043_, 0);
lean_dec(v_unused_2051_);
v___x_2045_ = v___x_2043_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v___x_2043_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2042_);
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2042_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
return v___x_2043_;
}
}
}
}
else
{
lean_dec(v___x_2030_);
lean_dec(v___x_2029_);
lean_dec(v_numNested_2021_);
lean_dec(v_all_2020_);
lean_dec(v_numParams_2019_);
lean_dec(v_indName_1806_);
return v___x_2031_;
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec(v_numNested_2021_);
lean_dec(v_all_2020_);
lean_dec(v_numParams_2019_);
lean_dec(v_indName_1806_);
v___x_2054_ = lean_box(0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2054_);
v___x_2056_ = v___x_2026_;
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
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_numNested_2021_);
lean_dec(v_all_2020_);
lean_dec(v_numParams_2019_);
lean_dec(v_indName_1806_);
v_a_2059_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2023_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2023_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_dec(v_a_2008_);
lean_dec(v_indName_1806_);
v___x_2067_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2067_);
v___x_2069_ = v___x_2010_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2067_);
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
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_indName_1806_);
v_a_2072_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2007_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2007_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
else
{
goto v___jp_1942_;
}
}
else
{
goto v___jp_1942_;
}
v___jp_1895_:
{
lean_object* v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; double v___x_1903_; double v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1899_ = lean_io_mono_nanos_now();
v___x_1900_ = lean_float_of_nat(v___y_1897_);
v___x_1901_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1902_ = lean_float_div(v___x_1900_, v___x_1901_);
v___x_1903_ = lean_float_of_nat(v___x_1899_);
v___x_1904_ = lean_float_div(v___x_1903_, v___x_1901_);
v___x_1905_ = lean_box_float(v___x_1902_);
v___x_1906_ = lean_box_float(v___x_1904_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1898_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1891_, v_hasTrace_1815_, v___x_1892_, v_options_1813_, v___x_1894_, v___y_1896_, v___f_1890_, v___x_1908_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
return v___x_1909_;
}
v___jp_1910_:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1913_);
v___y_1896_ = v___y_1911_;
v___y_1897_ = v___y_1912_;
v_a_1898_ = v___x_1914_;
goto v___jp_1895_;
}
v___jp_1915_:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1918_);
v___y_1896_ = v___y_1916_;
v___y_1897_ = v___y_1917_;
v_a_1898_ = v___x_1919_;
goto v___jp_1895_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; double v___x_1925_; double v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1924_ = lean_io_get_num_heartbeats();
v___x_1925_ = lean_float_of_nat(v___y_1921_);
v___x_1926_ = lean_float_of_nat(v___x_1924_);
v___x_1927_ = lean_box_float(v___x_1925_);
v___x_1928_ = lean_box_float(v___x_1926_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1923_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1891_, v_hasTrace_1815_, v___x_1892_, v_options_1813_, v___x_1894_, v___y_1922_, v___f_1890_, v___x_1930_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
return v___x_1931_;
}
v___jp_1932_:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1935_);
v___y_1921_ = v___y_1933_;
v___y_1922_ = v___y_1934_;
v_a_1923_ = v___x_1936_;
goto v___jp_1920_;
}
v___jp_1937_:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1940_);
v___y_1921_ = v___y_1938_;
v___y_1922_ = v___y_1939_;
v_a_1923_ = v___x_1941_;
goto v___jp_1920_;
}
v___jp_1942_:
{
lean_object* v___x_1943_; lean_object* v_a_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1943_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1810_);
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1943_);
v___x_1945_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1946_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1813_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1806_);
v___x_1948_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
if (lean_obj_tag(v_a_1949_) == 5)
{
lean_object* v_val_1950_; uint8_t v_isRec_1951_; 
v_val_1950_ = lean_ctor_get(v_a_1949_, 0);
lean_inc_ref(v_val_1950_);
lean_dec_ref_known(v_a_1949_, 1);
v_isRec_1951_ = lean_ctor_get_uint8(v_val_1950_, sizeof(void*)*6);
if (v_isRec_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref(v_val_1950_);
lean_dec(v_indName_1806_);
v___x_1952_ = lean_box(0);
v___y_1911_ = v_a_1944_;
v___y_1912_ = v___x_1947_;
v_a_1913_ = v___x_1952_;
goto v___jp_1910_;
}
else
{
lean_object* v_toConstantVal_1953_; lean_object* v_numParams_1954_; lean_object* v_all_1955_; lean_object* v_numNested_1956_; lean_object* v_type_1957_; lean_object* v___x_1958_; 
v_toConstantVal_1953_ = lean_ctor_get(v_val_1950_, 0);
lean_inc_ref(v_toConstantVal_1953_);
v_numParams_1954_ = lean_ctor_get(v_val_1950_, 1);
lean_inc(v_numParams_1954_);
v_all_1955_ = lean_ctor_get(v_val_1950_, 3);
lean_inc(v_all_1955_);
v_numNested_1956_ = lean_ctor_get(v_val_1950_, 5);
lean_inc(v_numNested_1956_);
lean_dec_ref(v_val_1950_);
v_type_1957_ = lean_ctor_get(v_toConstantVal_1953_, 2);
lean_inc_ref(v_type_1957_);
lean_dec_ref(v_toConstantVal_1953_);
v___x_1958_ = l_Lean_Meta_isPropFormerType(v_type_1957_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; uint8_t v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = lean_unbox(v_a_1959_);
lean_dec(v_a_1959_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_inc_n(v_indName_1806_, 2);
v___x_1961_ = l_Lean_mkRecName(v_indName_1806_);
v___x_1962_ = l_Lean_mkBelowName(v_indName_1806_);
lean_inc(v___x_1962_);
lean_inc(v_numParams_1954_);
lean_inc(v___x_1961_);
v___x_1963_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1961_, v_numParams_1954_, v___x_1962_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
lean_dec_ref_known(v___x_1963_, 1);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = l_List_get_x21Internal___redArg(v___x_1816_, v_all_1955_, v___x_1964_);
lean_dec(v_all_1955_);
v___x_1966_ = lean_name_eq(v___x_1965_, v_indName_1806_);
lean_dec(v_indName_1806_);
lean_dec(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v___x_1962_);
lean_dec(v___x_1961_);
lean_dec(v_numNested_1956_);
lean_dec(v_numParams_1954_);
v___x_1967_ = lean_box(0);
v___y_1911_ = v_a_1944_;
v___y_1912_ = v___x_1947_;
v_a_1913_ = v___x_1967_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_box(0);
v___x_1969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1956_, v___x_1961_, v___x_1962_, v_numParams_1954_, v___x_1964_, v___x_1968_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_numNested_1956_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_dec_ref_known(v___x_1969_, 1);
v___y_1911_ = v_a_1944_;
v___y_1912_ = v___x_1947_;
v_a_1913_ = v___x_1968_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___y_1916_ = v_a_1944_;
v___y_1917_ = v___x_1947_;
v_a_1918_ = v_a_1970_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v_a_1971_; 
lean_dec(v___x_1962_);
lean_dec(v___x_1961_);
lean_dec(v_numNested_1956_);
lean_dec(v_all_1955_);
lean_dec(v_numParams_1954_);
lean_dec(v_indName_1806_);
v_a_1971_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1963_, 1);
v___y_1916_ = v_a_1944_;
v___y_1917_ = v___x_1947_;
v_a_1918_ = v_a_1971_;
goto v___jp_1915_;
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v_numNested_1956_);
lean_dec(v_all_1955_);
lean_dec(v_numParams_1954_);
lean_dec(v_indName_1806_);
v___x_1972_ = lean_box(0);
v___y_1911_ = v_a_1944_;
v___y_1912_ = v___x_1947_;
v_a_1913_ = v___x_1972_;
goto v___jp_1910_;
}
}
else
{
lean_object* v_a_1973_; 
lean_dec(v_numNested_1956_);
lean_dec(v_all_1955_);
lean_dec(v_numParams_1954_);
lean_dec(v_indName_1806_);
v_a_1973_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1916_ = v_a_1944_;
v___y_1917_ = v___x_1947_;
v_a_1918_ = v_a_1973_;
goto v___jp_1915_;
}
}
}
else
{
lean_object* v___x_1974_; 
lean_dec(v_a_1949_);
lean_dec(v_indName_1806_);
v___x_1974_ = lean_box(0);
v___y_1911_ = v_a_1944_;
v___y_1912_ = v___x_1947_;
v_a_1913_ = v___x_1974_;
goto v___jp_1910_;
}
}
else
{
lean_object* v_a_1975_; 
lean_dec(v_indName_1806_);
v_a_1975_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1948_, 1);
v___y_1916_ = v_a_1944_;
v___y_1917_ = v___x_1947_;
v_a_1918_ = v_a_1975_;
goto v___jp_1915_;
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1806_);
v___x_1977_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
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
lean_dec(v_indName_1806_);
v___x_1981_ = lean_box(0);
v___y_1933_ = v___x_1976_;
v___y_1934_ = v_a_1944_;
v_a_1935_ = v___x_1981_;
goto v___jp_1932_;
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
v___x_1987_ = l_Lean_Meta_isPropFormerType(v_type_1986_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
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
lean_inc_n(v_indName_1806_, 2);
v___x_1990_ = l_Lean_mkRecName(v_indName_1806_);
v___x_1991_ = l_Lean_mkBelowName(v_indName_1806_);
lean_inc(v___x_1991_);
lean_inc(v_numParams_1983_);
lean_inc(v___x_1990_);
v___x_1992_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1990_, v_numParams_1983_, v___x_1991_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_dec_ref_known(v___x_1992_, 1);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_List_get_x21Internal___redArg(v___x_1816_, v_all_1984_, v___x_1993_);
lean_dec(v_all_1984_);
v___x_1995_ = lean_name_eq(v___x_1994_, v_indName_1806_);
lean_dec(v_indName_1806_);
lean_dec(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
lean_dec(v_numNested_1985_);
lean_dec(v_numParams_1983_);
v___x_1996_ = lean_box(0);
v___y_1933_ = v___x_1976_;
v___y_1934_ = v_a_1944_;
v_a_1935_ = v___x_1996_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1985_, v___x_1990_, v___x_1991_, v_numParams_1983_, v___x_1993_, v___x_1997_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_numNested_1985_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref_known(v___x_1998_, 1);
v___y_1933_ = v___x_1976_;
v___y_1934_ = v_a_1944_;
v_a_1935_ = v___x_1997_;
goto v___jp_1932_;
}
else
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___y_1938_ = v___x_1976_;
v___y_1939_ = v_a_1944_;
v_a_1940_ = v_a_1999_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v_a_2000_; 
lean_dec(v___x_1991_);
lean_dec(v___x_1990_);
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1806_);
v_a_2000_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1992_, 1);
v___y_1938_ = v___x_1976_;
v___y_1939_ = v_a_1944_;
v_a_1940_ = v_a_2000_;
goto v___jp_1937_;
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1806_);
v___x_2001_ = lean_box(0);
v___y_1933_ = v___x_1976_;
v___y_1934_ = v_a_1944_;
v_a_1935_ = v___x_2001_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_2002_; 
lean_dec(v_numNested_1985_);
lean_dec(v_all_1984_);
lean_dec(v_numParams_1983_);
lean_dec(v_indName_1806_);
v_a_2002_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_1987_, 1);
v___y_1938_ = v___x_1976_;
v___y_1939_ = v_a_1944_;
v_a_1940_ = v_a_2002_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v___x_2003_; 
lean_dec(v_a_1978_);
lean_dec(v_indName_1806_);
v___x_2003_ = lean_box(0);
v___y_1933_ = v___x_1976_;
v___y_1934_ = v_a_1944_;
v_a_1935_ = v___x_2003_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_2004_; 
lean_dec(v_indName_1806_);
v_a_2004_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_1977_, 1);
v___y_1938_ = v___x_1976_;
v___y_1939_ = v_a_1944_;
v_a_1940_ = v_a_2004_;
goto v___jp_1937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_mkBelow(v_indName_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2087_, lean_object* v___x_2088_, lean_object* v___x_2089_, lean_object* v___x_2090_, lean_object* v_inst_2091_, lean_object* v_R_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_, lean_object* v_c_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2087_, v___x_2088_, v___x_2089_, v___x_2090_, v_a_2093_, v_b_2094_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2102_, lean_object* v___x_2103_, lean_object* v___x_2104_, lean_object* v___x_2105_, lean_object* v_inst_2106_, lean_object* v_R_2107_, lean_object* v_a_2108_, lean_object* v_b_2109_, lean_object* v_c_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2102_, v___x_2103_, v___x_2104_, v___x_2105_, v_inst_2106_, v_R_2107_, v_a_2108_, v_b_2109_, v_c_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v_upperBound_2102_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2118_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2125_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
if (lean_obj_tag(v_a_2133_) == 0)
{
lean_object* v___x_2135_; 
v___x_2135_ = l_List_reverse___redArg(v_a_2134_);
return v___x_2135_;
}
else
{
lean_object* v_head_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2146_; 
v_head_2136_ = lean_ctor_get(v_a_2133_, 0);
v_tail_2137_ = lean_ctor_get(v_a_2133_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v_a_2133_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2139_ = v_a_2133_;
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_head_2136_);
lean_dec(v_a_2133_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2146_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = l_Lean_MessageData_ofExpr(v_head_2136_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_a_2134_);
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_a_2134_);
v___x_2143_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
v_a_2133_ = v_tail_2137_;
v_a_2134_ = v___x_2143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2147_, lean_object* v_v_2148_, lean_object* v_i_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = lean_array_get_size(v_xs_2147_);
v___x_2151_ = lean_nat_dec_lt(v_i_2149_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; 
lean_dec(v_i_2149_);
v___x_2152_ = lean_box(0);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = lean_array_fget_borrowed(v_xs_2147_, v_i_2149_);
v___x_2154_ = lean_expr_eqv(v___x_2153_, v_v_2148_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_add(v_i_2149_, v___x_2155_);
lean_dec(v_i_2149_);
v_i_2149_ = v___x_2156_;
goto _start;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_i_2149_);
return v___x_2158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2159_, lean_object* v_v_2160_, lean_object* v_i_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2159_, v_v_2160_, v_i_2161_);
lean_dec_ref(v_v_2160_);
lean_dec_ref(v_xs_2159_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2163_, lean_object* v_v_2164_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2163_, v_v_2164_, v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2167_, lean_object* v_v_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2167_, v_v_2168_);
lean_dec_ref(v_v_2168_);
lean_dec_ref(v_xs_2167_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2170_, lean_object* v_v_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2170_, v_v_2171_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_box(0);
return v___x_2173_;
}
else
{
lean_object* v_val_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_val_2174_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2172_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_val_2174_);
lean_dec(v___x_2172_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_val_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2182_, lean_object* v_v_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2182_, v_v_2183_);
lean_dec_ref(v_v_2183_);
lean_dec_ref(v_xs_2182_);
return v_res_2184_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2191_, lean_object* v_prods_2192_, lean_object* v_motives_2193_, lean_object* v_fs_2194_, lean_object* v_minor__type_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 5)
{
lean_object* v_fn_2204_; lean_object* v_arg_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_fn_2204_ = lean_ctor_get(v_x_2196_, 0);
lean_inc_ref(v_fn_2204_);
v_arg_2205_ = lean_ctor_get(v_x_2196_, 1);
lean_inc_ref(v_arg_2205_);
lean_dec_ref_known(v_x_2196_, 2);
v___x_2206_ = lean_array_set(v_x_2197_, v_x_2198_, v_arg_2205_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v_x_2198_, v___x_2207_);
lean_dec(v_x_2198_);
v_x_2196_ = v_fn_2204_;
v_x_2197_ = v___x_2206_;
v_x_2198_ = v___x_2208_;
goto _start;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec(v_x_2198_);
v___x_2210_ = l_Lean_instInhabitedExpr;
v___x_2211_ = l_Lean_Meta_PProdN_mk(v_rlvl_2191_, v_prods_2192_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2193_, v_x_2196_);
lean_dec_ref(v_x_2196_);
if (lean_obj_tag(v___x_2213_) == 1)
{
lean_object* v_val_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v_minor__type_2195_);
lean_dec_ref(v_motives_2193_);
v_val_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_val_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = lean_array_get_borrowed(v___x_2210_, v_fs_2194_, v_val_2214_);
lean_dec(v_val_2214_);
lean_inc(v_a_2212_);
v___x_2216_ = lean_array_push(v_x_2197_, v_a_2212_);
lean_inc(v___x_2215_);
v___x_2217_ = l_Lean_mkAppN(v___x_2215_, v___x_2216_);
lean_dec_ref(v___x_2216_);
v___x_2218_ = l_Lean_Meta_mkPProdMk(v___x_2217_, v_a_2212_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2218_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec(v___x_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_x_2197_);
v___x_2219_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2220_ = l_Lean_MessageData_ofExpr(v_minor__type_2195_);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_array_to_list(v_motives_2193_);
v___x_2225_ = lean_box(0);
v___x_2226_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2224_, v___x_2225_);
v___x_2227_ = l_Lean_MessageData_ofList(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2223_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2228_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2229_;
}
}
else
{
lean_dec_ref(v_x_2197_);
lean_dec_ref(v_x_2196_);
lean_dec_ref(v_minor__type_2195_);
lean_dec_ref(v_motives_2193_);
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2230_, lean_object* v_prods_2231_, lean_object* v_motives_2232_, lean_object* v_fs_2233_, lean_object* v_minor__type_2234_, lean_object* v_x_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2230_, v_prods_2231_, v_motives_2232_, v_fs_2233_, v_minor__type_2234_, v_x_2235_, v_x_2236_, v_x_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v_fs_2233_);
return v_res_2243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2244_; lean_object* v_dummy_2245_; 
v___x_2244_ = lean_box(0);
v_dummy_2245_ = l_Lean_Expr_sort___override(v___x_2244_);
return v_dummy_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2246_, lean_object* v_head_2247_, lean_object* v_belows_2248_, lean_object* v_prods_2249_, lean_object* v_rlvl_2250_, lean_object* v_fs_2251_, lean_object* v_minor__type_2252_, lean_object* v_tail_2253_, lean_object* v_arg__args_2254_, lean_object* v_arg__type_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2246_, v_head_2247_, v_belows_2248_, v_prods_2249_, v_rlvl_2250_, v_fs_2251_, v_minor__type_2252_, v_tail_2253_, v_arg__args_2254_, v_arg__type_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_arg__args_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2262_, lean_object* v_motives_2263_, lean_object* v_belows_2264_, lean_object* v_fs_2265_, lean_object* v_minor__type_2266_, lean_object* v_prods_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
if (lean_obj_tag(v_a_2268_) == 0)
{
lean_object* v_dummy_2274_; lean_object* v_nargs_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v_belows_2264_);
v_dummy_2274_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2275_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2266_);
lean_inc(v_nargs_2275_);
v___x_2276_ = lean_mk_array(v_nargs_2275_, v_dummy_2274_);
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_sub(v_nargs_2275_, v___x_2277_);
lean_dec(v_nargs_2275_);
lean_inc_ref(v_minor__type_2266_);
v___x_2279_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2262_, v_prods_2267_, v_motives_2263_, v_fs_2265_, v_minor__type_2266_, v_minor__type_2266_, v___x_2276_, v___x_2278_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
lean_dec_ref(v_fs_2265_);
return v___x_2279_;
}
else
{
lean_object* v_head_2280_; lean_object* v_tail_2281_; lean_object* v___f_2282_; lean_object* v___x_2283_; 
v_head_2280_ = lean_ctor_get(v_a_2268_, 0);
lean_inc_n(v_head_2280_, 2);
v_tail_2281_ = lean_ctor_get(v_a_2268_, 1);
lean_inc(v_tail_2281_);
lean_dec_ref_known(v_a_2268_, 2);
v___f_2282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2282_, 0, v_motives_2263_);
lean_closure_set(v___f_2282_, 1, v_head_2280_);
lean_closure_set(v___f_2282_, 2, v_belows_2264_);
lean_closure_set(v___f_2282_, 3, v_prods_2267_);
lean_closure_set(v___f_2282_, 4, v_rlvl_2262_);
lean_closure_set(v___f_2282_, 5, v_fs_2265_);
lean_closure_set(v___f_2282_, 6, v_minor__type_2266_);
lean_closure_set(v___f_2282_, 7, v_tail_2281_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_a_2269_);
v___x_2283_ = lean_infer_type(v_head_2280_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v___x_2285_ = 0;
v___x_2286_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2284_, v___f_2282_, v___x_2285_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_);
return v___x_2286_;
}
else
{
lean_dec_ref(v___f_2282_);
return v___x_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2287_, lean_object* v_rlvl_2288_, lean_object* v_motives_2289_, lean_object* v_belows_2290_, lean_object* v_fs_2291_, lean_object* v_minor__type_2292_, lean_object* v_tail_2293_, uint8_t v___x_2294_, uint8_t v___x_2295_, uint8_t v___x_2296_, lean_object* v_arg_x27_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_inc_ref(v_arg_x27_2297_);
v___x_2303_ = lean_array_push(v_prods_2287_, v_arg_x27_2297_);
v___x_2304_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2288_, v_motives_2289_, v_belows_2290_, v_fs_2291_, v_minor__type_2292_, v___x_2303_, v_tail_2293_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = lean_unsigned_to_nat(1u);
v___x_2307_ = lean_mk_empty_array_with_capacity(v___x_2306_);
v___x_2308_ = lean_array_push(v___x_2307_, v_arg_x27_2297_);
v___x_2309_ = l_Lean_Meta_mkLambdaFVars(v___x_2308_, v_a_2305_, v___x_2294_, v___x_2295_, v___x_2294_, v___x_2295_, v___x_2296_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec_ref(v___x_2308_);
return v___x_2309_;
}
else
{
lean_dec_ref(v_arg_x27_2297_);
return v___x_2304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2310_, lean_object* v_rlvl_2311_, lean_object* v_motives_2312_, lean_object* v_belows_2313_, lean_object* v_fs_2314_, lean_object* v_minor__type_2315_, lean_object* v_tail_2316_, lean_object* v___x_2317_, lean_object* v___x_2318_, lean_object* v___x_2319_, lean_object* v_arg_x27_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___x_1689__boxed_2326_; uint8_t v___x_1690__boxed_2327_; uint8_t v___x_1691__boxed_2328_; lean_object* v_res_2329_; 
v___x_1689__boxed_2326_ = lean_unbox(v___x_2317_);
v___x_1690__boxed_2327_ = lean_unbox(v___x_2318_);
v___x_1691__boxed_2328_ = lean_unbox(v___x_2319_);
v_res_2329_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2310_, v_rlvl_2311_, v_motives_2312_, v_belows_2313_, v_fs_2314_, v_minor__type_2315_, v_tail_2316_, v___x_1689__boxed_2326_, v___x_1690__boxed_2327_, v___x_1691__boxed_2328_, v_arg_x27_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2330_, lean_object* v_head_2331_, lean_object* v_belows_2332_, lean_object* v_arg__type_2333_, lean_object* v_prods_2334_, lean_object* v_rlvl_2335_, lean_object* v_fs_2336_, lean_object* v_minor__type_2337_, lean_object* v_tail_2338_, lean_object* v_arg__args_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
if (lean_obj_tag(v_x_2340_) == 5)
{
lean_object* v_fn_2348_; lean_object* v_arg_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_fn_2348_ = lean_ctor_get(v_x_2340_, 0);
lean_inc_ref(v_fn_2348_);
v_arg_2349_ = lean_ctor_get(v_x_2340_, 1);
lean_inc_ref(v_arg_2349_);
lean_dec_ref_known(v_x_2340_, 2);
v___x_2350_ = lean_array_set(v_x_2341_, v_x_2342_, v_arg_2349_);
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_nat_sub(v_x_2342_, v___x_2351_);
lean_dec(v_x_2342_);
v_x_2340_ = v_fn_2348_;
v_x_2341_ = v___x_2350_;
v_x_2342_ = v___x_2352_;
goto _start;
}
else
{
lean_object* v___x_2354_; 
lean_dec(v_x_2342_);
v___x_2354_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2330_, v_x_2340_);
lean_dec_ref(v_x_2340_);
if (lean_obj_tag(v___x_2354_) == 1)
{
lean_object* v_val_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v_val_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v___x_2354_, 1);
v___x_2356_ = l_Lean_instInhabitedExpr;
v___x_2357_ = l_Lean_Expr_fvarId_x21(v_head_2331_);
lean_dec_ref(v_head_2331_);
v___x_2358_ = l_Lean_FVarId_getUserName___redArg(v___x_2357_, v___y_2343_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = lean_array_get_borrowed(v___x_2356_, v_belows_2332_, v_val_2355_);
lean_dec(v_val_2355_);
lean_inc(v___x_2360_);
v___x_2361_ = l_Lean_mkAppN(v___x_2360_, v_x_2341_);
lean_dec_ref(v_x_2341_);
v___x_2362_ = l_Lean_Meta_mkPProd(v_arg__type_2333_, v___x_2361_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; uint8_t v___x_2364_; uint8_t v___x_2365_; uint8_t v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = 0;
v___x_2365_ = 1;
v___x_2366_ = 1;
v___x_2367_ = lean_box(v___x_2364_);
v___x_2368_ = lean_box(v___x_2365_);
v___x_2369_ = lean_box(v___x_2366_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2370_, 0, v_prods_2334_);
lean_closure_set(v___f_2370_, 1, v_rlvl_2335_);
lean_closure_set(v___f_2370_, 2, v_motives_2330_);
lean_closure_set(v___f_2370_, 3, v_belows_2332_);
lean_closure_set(v___f_2370_, 4, v_fs_2336_);
lean_closure_set(v___f_2370_, 5, v_minor__type_2337_);
lean_closure_set(v___f_2370_, 6, v_tail_2338_);
lean_closure_set(v___f_2370_, 7, v___x_2367_);
lean_closure_set(v___f_2370_, 8, v___x_2368_);
lean_closure_set(v___f_2370_, 9, v___x_2369_);
v___x_2371_ = l_Lean_Meta_mkForallFVars(v_arg__args_2339_, v_a_2363_, v___x_2364_, v___x_2365_, v___x_2365_, v___x_2366_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2359_, v_a_2372_, v___f_2370_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2373_;
}
else
{
lean_dec_ref(v___f_2370_);
lean_dec(v_a_2359_);
return v___x_2371_;
}
}
else
{
lean_dec(v_a_2359_);
lean_dec(v_tail_2338_);
lean_dec_ref(v_minor__type_2337_);
lean_dec_ref(v_fs_2336_);
lean_dec(v_rlvl_2335_);
lean_dec_ref(v_prods_2334_);
lean_dec_ref(v_belows_2332_);
lean_dec_ref(v_motives_2330_);
return v___x_2362_;
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_val_2355_);
lean_dec_ref(v_x_2341_);
lean_dec(v_tail_2338_);
lean_dec_ref(v_minor__type_2337_);
lean_dec_ref(v_fs_2336_);
lean_dec(v_rlvl_2335_);
lean_dec_ref(v_prods_2334_);
lean_dec_ref(v_arg__type_2333_);
lean_dec_ref(v_belows_2332_);
lean_dec_ref(v_motives_2330_);
v_a_2374_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2358_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2358_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v___x_2382_; 
lean_dec(v___x_2354_);
lean_dec_ref(v_x_2341_);
lean_dec_ref(v_arg__type_2333_);
v___x_2382_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2335_, v_motives_2330_, v_belows_2332_, v_fs_2336_, v_minor__type_2337_, v_prods_2334_, v_tail_2338_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; uint8_t v___x_2388_; uint8_t v___x_2389_; lean_object* v___x_2390_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_mk_empty_array_with_capacity(v___x_2384_);
v___x_2386_ = lean_array_push(v___x_2385_, v_head_2331_);
v___x_2387_ = 0;
v___x_2388_ = 1;
v___x_2389_ = 1;
v___x_2390_ = l_Lean_Meta_mkLambdaFVars(v___x_2386_, v_a_2383_, v___x_2387_, v___x_2388_, v___x_2387_, v___x_2388_, v___x_2389_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec_ref(v___x_2386_);
return v___x_2390_;
}
else
{
lean_dec_ref(v_head_2331_);
return v___x_2382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2391_, lean_object* v_head_2392_, lean_object* v_belows_2393_, lean_object* v_prods_2394_, lean_object* v_rlvl_2395_, lean_object* v_fs_2396_, lean_object* v_minor__type_2397_, lean_object* v_tail_2398_, lean_object* v_arg__args_2399_, lean_object* v_arg__type_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_dummy_2406_; lean_object* v_nargs_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_dummy_2406_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2407_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2400_);
lean_inc(v_nargs_2407_);
v___x_2408_ = lean_mk_array(v_nargs_2407_, v_dummy_2406_);
v___x_2409_ = lean_unsigned_to_nat(1u);
v___x_2410_ = lean_nat_sub(v_nargs_2407_, v___x_2409_);
lean_dec(v_nargs_2407_);
lean_inc_ref(v_arg__type_2400_);
v___x_2411_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2391_, v_head_2392_, v_belows_2393_, v_arg__type_2400_, v_prods_2394_, v_rlvl_2395_, v_fs_2396_, v_minor__type_2397_, v_tail_2398_, v_arg__args_2399_, v_arg__type_2400_, v___x_2408_, v___x_2410_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2412_, lean_object* v_motives_2413_, lean_object* v_belows_2414_, lean_object* v_fs_2415_, lean_object* v_minor__type_2416_, lean_object* v_prods_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2412_, v_motives_2413_, v_belows_2414_, v_fs_2415_, v_minor__type_2416_, v_prods_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2425_ = _args[0];
lean_object* v_head_2426_ = _args[1];
lean_object* v_belows_2427_ = _args[2];
lean_object* v_arg__type_2428_ = _args[3];
lean_object* v_prods_2429_ = _args[4];
lean_object* v_rlvl_2430_ = _args[5];
lean_object* v_fs_2431_ = _args[6];
lean_object* v_minor__type_2432_ = _args[7];
lean_object* v_tail_2433_ = _args[8];
lean_object* v_arg__args_2434_ = _args[9];
lean_object* v_x_2435_ = _args[10];
lean_object* v_x_2436_ = _args[11];
lean_object* v_x_2437_ = _args[12];
lean_object* v___y_2438_ = _args[13];
lean_object* v___y_2439_ = _args[14];
lean_object* v___y_2440_ = _args[15];
lean_object* v___y_2441_ = _args[16];
lean_object* v___y_2442_ = _args[17];
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2425_, v_head_2426_, v_belows_2427_, v_arg__type_2428_, v_prods_2429_, v_rlvl_2430_, v_fs_2431_, v_minor__type_2432_, v_tail_2433_, v_arg__args_2434_, v_x_2435_, v_x_2436_, v_x_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_arg__args_2434_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2444_, lean_object* v_motives_2445_, lean_object* v_belows_2446_, lean_object* v_fs_2447_, lean_object* v_minor__args_2448_, lean_object* v_minor__type_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2456_ = lean_array_to_list(v_minor__args_2448_);
v___x_2457_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2444_, v_motives_2445_, v_belows_2446_, v_fs_2447_, v_minor__type_2449_, v___x_2455_, v___x_2456_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2458_, lean_object* v_motives_2459_, lean_object* v_belows_2460_, lean_object* v_fs_2461_, lean_object* v_minor__args_2462_, lean_object* v_minor__type_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2458_, v_motives_2459_, v_belows_2460_, v_fs_2461_, v_minor__args_2462_, v_minor__type_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2470_, lean_object* v_motives_2471_, lean_object* v_belows_2472_, lean_object* v_fs_2473_, lean_object* v_minorType_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v___f_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; 
v___f_2480_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2480_, 0, v_rlvl_2470_);
lean_closure_set(v___f_2480_, 1, v_motives_2471_);
lean_closure_set(v___f_2480_, 2, v_belows_2472_);
lean_closure_set(v___f_2480_, 3, v_fs_2473_);
v___x_2481_ = 0;
v___x_2482_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2474_, v___f_2480_, v___x_2481_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2483_, lean_object* v_motives_2484_, lean_object* v_belows_2485_, lean_object* v_fs_2486_, lean_object* v_minorType_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2483_, v_motives_2484_, v_belows_2485_, v_fs_2486_, v_minorType_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___f_2500_; lean_object* v___x_27956__overap_2501_; lean_object* v___x_2502_; 
v___f_2500_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27956__overap_2501_ = lean_panic_fn_borrowed(v___f_2500_, v_msg_2494_);
lean_inc(v___y_2498_);
lean_inc_ref(v___y_2497_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
v___x_2502_ = lean_apply_5(v___x_27956__overap_2501_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, lean_box(0));
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v___x_2513_; 
v___x_2513_ = l_Lean_Expr_hasMVar(v_e_2510_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_e_2510_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; lean_object* v_mctx_2516_; lean_object* v___x_2517_; lean_object* v_fst_2518_; lean_object* v_snd_2519_; lean_object* v___x_2520_; lean_object* v_cache_2521_; lean_object* v_zetaDeltaFVarIds_2522_; lean_object* v_postponed_2523_; lean_object* v_diag_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
v___x_2515_ = lean_st_ref_get(v___y_2511_);
v_mctx_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_mctx_2516_);
lean_dec(v___x_2515_);
v___x_2517_ = l_Lean_instantiateMVarsCore(v_mctx_2516_, v_e_2510_);
v_fst_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_fst_2518_);
v_snd_2519_ = lean_ctor_get(v___x_2517_, 1);
lean_inc(v_snd_2519_);
lean_dec_ref(v___x_2517_);
v___x_2520_ = lean_st_ref_take(v___y_2511_);
v_cache_2521_ = lean_ctor_get(v___x_2520_, 1);
v_zetaDeltaFVarIds_2522_ = lean_ctor_get(v___x_2520_, 2);
v_postponed_2523_ = lean_ctor_get(v___x_2520_, 3);
v_diag_2524_ = lean_ctor_get(v___x_2520_, 4);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2520_, 0);
lean_dec(v_unused_2534_);
v___x_2526_ = v___x_2520_;
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_diag_2524_);
lean_inc(v_postponed_2523_);
lean_inc(v_zetaDeltaFVarIds_2522_);
lean_inc(v_cache_2521_);
lean_dec(v___x_2520_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v_snd_2519_);
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_snd_2519_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_cache_2521_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_zetaDeltaFVarIds_2522_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_postponed_2523_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_diag_2524_);
v___x_2529_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_st_ref_put(v___y_2511_, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v_fst_2518_);
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2535_, v___y_2536_);
lean_dec(v___y_2536_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2539_, v___y_2541_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; lean_object* v_env_2557_; lean_object* v_toConstantVal_2558_; lean_object* v_value_2559_; lean_object* v_all_2560_; lean_object* v_type_2567_; uint8_t v___x_2568_; 
v___x_2556_ = lean_st_ref_get(v___y_2554_);
v_env_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref_n(v_env_2557_, 2);
lean_dec(v___x_2556_);
v_toConstantVal_2558_ = lean_ctor_get(v_thm_2553_, 0);
v_value_2559_ = lean_ctor_get(v_thm_2553_, 1);
v_all_2560_ = lean_ctor_get(v_thm_2553_, 2);
v_type_2567_ = lean_ctor_get(v_toConstantVal_2558_, 2);
v___x_2568_ = l_Lean_Environment_hasUnsafe(v_env_2557_, v_type_2567_);
if (v___x_2568_ == 0)
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_Environment_hasUnsafe(v_env_2557_, v_value_2559_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_thm_2553_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
else
{
lean_inc(v_all_2560_);
lean_inc_ref(v_value_2559_);
lean_inc_ref(v_toConstantVal_2558_);
lean_dec_ref(v_thm_2553_);
goto v___jp_2561_;
}
}
else
{
lean_inc(v_all_2560_);
lean_inc_ref(v_value_2559_);
lean_inc_ref(v_toConstantVal_2558_);
lean_dec_ref(v_env_2557_);
lean_dec_ref(v_thm_2553_);
goto v___jp_2561_;
}
v___jp_2561_:
{
lean_object* v___x_2562_; uint8_t v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = lean_box(0);
v___x_2563_ = 0;
v___x_2564_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2564_, 0, v_toConstantVal_2558_);
lean_ctor_set(v___x_2564_, 1, v_value_2559_);
lean_ctor_set(v___x_2564_, 2, v___x_2562_);
lean_ctor_set(v___x_2564_, 3, v_all_2560_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*4, v___x_2563_);
v___x_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2572_, v___y_2573_);
lean_dec(v___y_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2576_, v___y_2580_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2591_, lean_object* v___x_2592_, lean_object* v___x_2593_, lean_object* v_all_2594_, lean_object* v___x_2595_, lean_object* v___x_2596_, lean_object* v___x_2597_, lean_object* v_x_2598_){
_start:
{
lean_object* v___y_2600_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2604_ = lean_array_get_size(v_all_2594_);
v___x_2605_ = lean_nat_dec_lt(v_x_2598_, v___x_2604_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2606_ = lean_array_get_borrowed(v___x_2595_, v_all_2594_, v___x_2596_);
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2608_ = lean_nat_sub(v_x_2598_, v___x_2604_);
v___x_2609_ = lean_nat_add(v___x_2608_, v___x_2597_);
lean_dec(v___x_2608_);
v___x_2610_ = l_Nat_reprFast(v___x_2609_);
v___x_2611_ = lean_string_append(v___x_2607_, v___x_2610_);
lean_dec_ref(v___x_2610_);
lean_inc(v___x_2606_);
v___x_2612_ = l_Lean_Name_str___override(v___x_2606_, v___x_2611_);
v___y_2600_ = v___x_2612_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_array_fget_borrowed(v_all_2594_, v_x_2598_);
lean_inc(v___x_2613_);
v___x_2614_ = l_Lean_mkBelowName(v___x_2613_);
v___y_2600_ = v___x_2614_;
goto v___jp_2599_;
}
v___jp_2599_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = l_Lean_Expr_const___override(v___y_2600_, v___x_2591_);
v___x_2602_ = l_Array_append___redArg(v___x_2592_, v___x_2593_);
v___x_2603_ = l_Lean_mkAppN(v___x_2601_, v___x_2602_);
lean_dec_ref(v___x_2602_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v___x_2617_, lean_object* v_all_2618_, lean_object* v___x_2619_, lean_object* v___x_2620_, lean_object* v___x_2621_, lean_object* v_x_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2615_, v___x_2616_, v___x_2617_, v_all_2618_, v___x_2619_, v___x_2620_, v___x_2621_, v_x_2622_);
lean_dec(v_x_2622_);
lean_dec(v___x_2621_);
lean_dec(v___x_2620_);
lean_dec(v___x_2619_);
lean_dec_ref(v_all_2618_);
lean_dec_ref(v___x_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v_fs_2627_, lean_object* v_as_2628_, size_t v_sz_2629_, size_t v_i_2630_, lean_object* v_b_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
uint8_t v___x_2637_; 
v___x_2637_ = lean_usize_dec_lt(v_i_2630_, v_sz_2629_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v_fs_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v___x_2625_);
lean_dec(v___x_2624_);
v___x_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_b_2631_);
return v___x_2638_;
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_array_uget_borrowed(v_as_2628_, v_i_2630_);
lean_inc(v___y_2635_);
lean_inc_ref(v___y_2634_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v_a_2639_);
v___x_2640_ = lean_infer_type(v_a_2639_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
lean_inc_ref(v_fs_2627_);
lean_inc_ref(v___x_2626_);
lean_inc_ref(v___x_2625_);
lean_inc(v___x_2624_);
v___x_2642_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2624_, v___x_2625_, v___x_2626_, v_fs_2627_, v_a_2641_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; size_t v___x_2645_; size_t v___x_2646_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = l_Lean_Expr_app___override(v_b_2631_, v_a_2643_);
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2630_, v___x_2645_);
v_i_2630_ = v___x_2646_;
v_b_2631_ = v___x_2644_;
goto _start;
}
else
{
lean_dec_ref(v_b_2631_);
lean_dec_ref(v_fs_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v___x_2625_);
lean_dec(v___x_2624_);
return v___x_2642_;
}
}
else
{
lean_dec_ref(v_b_2631_);
lean_dec_ref(v_fs_2627_);
lean_dec_ref(v___x_2626_);
lean_dec_ref(v___x_2625_);
lean_dec(v___x_2624_);
return v___x_2640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_fs_2651_, lean_object* v_as_2652_, lean_object* v_sz_2653_, lean_object* v_i_2654_, lean_object* v_b_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
size_t v_sz_boxed_2661_; size_t v_i_boxed_2662_; lean_object* v_res_2663_; 
v_sz_boxed_2661_ = lean_unbox_usize(v_sz_2653_);
lean_dec(v_sz_2653_);
v_i_boxed_2662_ = lean_unbox_usize(v_i_2654_);
lean_dec(v_i_2654_);
v_res_2663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2648_, v___x_2649_, v___x_2650_, v_fs_2651_, v_as_2652_, v_sz_boxed_2661_, v_i_boxed_2662_, v_b_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec_ref(v_as_2652_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2664_, lean_object* v___x_2665_, uint8_t v___x_2666_, lean_object* v_targs_2667_, lean_object* v_x_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = l_Lean_mkAppN(v_a_2664_, v_targs_2667_);
v___x_2675_ = l_Lean_mkAppN(v___x_2665_, v_targs_2667_);
v___x_2676_ = l_Lean_Meta_mkPProd(v___x_2674_, v___x_2675_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; uint8_t v___x_2678_; uint8_t v___x_2679_; lean_object* v___x_2680_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = 0;
v___x_2679_ = 1;
v___x_2680_ = l_Lean_Meta_mkLambdaFVars(v_targs_2667_, v_a_2677_, v___x_2678_, v___x_2666_, v___x_2678_, v___x_2666_, v___x_2679_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
return v___x_2680_;
}
else
{
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v_targs_2684_, lean_object* v_x_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_31228__boxed_2691_; lean_object* v_res_2692_; 
v___x_31228__boxed_2691_ = lean_unbox(v___x_2683_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2681_, v___x_2682_, v___x_31228__boxed_2691_, v_targs_2684_, v_x_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_x_2685_);
lean_dec_ref(v_targs_2684_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2693_, lean_object* v___x_2694_, lean_object* v_as_2695_, size_t v_sz_2696_, size_t v_i_2697_, lean_object* v_b_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
uint8_t v___x_2704_; 
v___x_2704_ = lean_usize_dec_lt(v_i_2697_, v_sz_2696_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_b_2698_);
return v___x_2705_;
}
else
{
lean_object* v_snd_2706_; lean_object* v_fst_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2764_; 
v_snd_2706_ = lean_ctor_get(v_b_2698_, 1);
v_fst_2707_ = lean_ctor_get(v_b_2698_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_b_2698_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2709_ = v_b_2698_;
v_isShared_2710_ = v_isSharedCheck_2764_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_snd_2706_);
lean_inc(v_fst_2707_);
lean_dec(v_b_2698_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2764_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_array_2711_; lean_object* v_start_2712_; lean_object* v_stop_2713_; uint8_t v___x_2714_; 
v_array_2711_ = lean_ctor_get(v_snd_2706_, 0);
v_start_2712_ = lean_ctor_get(v_snd_2706_, 1);
v_stop_2713_ = lean_ctor_get(v_snd_2706_, 2);
v___x_2714_ = lean_nat_dec_lt(v_start_2712_, v_stop_2713_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2716_; 
if (v_isShared_2710_ == 0)
{
v___x_2716_ = v___x_2709_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_fst_2707_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_snd_2706_);
v___x_2716_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; 
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
}
else
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2760_; 
lean_inc(v_stop_2713_);
lean_inc(v_start_2712_);
lean_inc_ref(v_array_2711_);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_snd_2706_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; lean_object* v_unused_2762_; lean_object* v_unused_2763_; 
v_unused_2761_ = lean_ctor_get(v_snd_2706_, 2);
lean_dec(v_unused_2761_);
v_unused_2762_ = lean_ctor_get(v_snd_2706_, 1);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_snd_2706_, 0);
lean_dec(v_unused_2763_);
v___x_2720_ = v_snd_2706_;
v_isShared_2721_ = v_isSharedCheck_2760_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v_snd_2706_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2760_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
uint8_t v___x_2722_; lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2722_ = lean_nat_dec_lt(v___x_2693_, v___x_2694_);
v_a_2723_ = lean_array_uget_borrowed(v_as_2695_, v_i_2697_);
v___x_2724_ = lean_array_fget_borrowed(v_array_2711_, v_start_2712_);
v___x_2725_ = lean_box(v___x_2722_);
lean_inc(v___x_2724_);
lean_inc(v_a_2723_);
v___f_2726_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2726_, 0, v_a_2723_);
lean_closure_set(v___f_2726_, 1, v___x_2724_);
lean_closure_set(v___f_2726_, 2, v___x_2725_);
v___x_2727_ = lean_unsigned_to_nat(1u);
v___x_2728_ = lean_nat_add(v_start_2712_, v___x_2727_);
lean_dec(v_start_2712_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 1, v___x_2728_);
v___x_2730_ = v___x_2720_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_array_2711_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_stop_2713_);
v___x_2730_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; 
lean_inc(v___y_2702_);
lean_inc_ref(v___y_2701_);
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc(v_a_2723_);
v___x_2731_ = lean_infer_type(v_a_2723_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = 0;
v___x_2734_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2732_, v___f_2726_, v___x_2733_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_Expr_app___override(v_fst_2707_, v_a_2735_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___x_2730_);
lean_ctor_set(v___x_2709_, 0, v___x_2736_);
v___x_2738_ = v___x_2709_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2730_);
v___x_2738_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
size_t v___x_2739_; size_t v___x_2740_; 
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2697_, v___x_2739_);
v_i_2697_ = v___x_2740_;
v_b_2698_ = v___x_2738_;
goto _start;
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v___x_2730_);
lean_del_object(v___x_2709_);
lean_dec(v_fst_2707_);
v_a_2743_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2734_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2734_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2758_; 
lean_dec_ref(v___x_2730_);
lean_dec_ref(v___f_2726_);
lean_del_object(v___x_2709_);
lean_dec(v_fst_2707_);
v_a_2751_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2753_ = v___x_2731_;
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2731_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2758_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2756_; 
if (v_isShared_2754_ == 0)
{
v___x_2756_ = v___x_2753_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_a_2751_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2765_, lean_object* v___x_2766_, lean_object* v_as_2767_, lean_object* v_sz_2768_, lean_object* v_i_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
size_t v_sz_boxed_2776_; size_t v_i_boxed_2777_; lean_object* v_res_2778_; 
v_sz_boxed_2776_ = lean_unbox_usize(v_sz_2768_);
lean_dec(v_sz_2768_);
v_i_boxed_2777_ = lean_unbox_usize(v_i_2769_);
lean_dec(v_i_2769_);
v_res_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2765_, v___x_2766_, v_as_2767_, v_sz_boxed_2776_, v_i_boxed_2777_, v_b_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec_ref(v_as_2767_);
lean_dec(v___x_2766_);
lean_dec(v___x_2765_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2779_, size_t v_sz_2780_, size_t v_i_2781_, lean_object* v_b_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2781_, v_sz_2780_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_b_2782_);
return v___x_2789_;
}
else
{
lean_object* v_a_2790_; lean_object* v_toInductionSubgoal_2791_; lean_object* v_mvarId_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2790_ = lean_array_uget_borrowed(v_as_2779_, v_i_2781_);
v_toInductionSubgoal_2791_ = lean_ctor_get(v_a_2790_, 0);
v_mvarId_2792_ = lean_ctor_get(v_toInductionSubgoal_2791_, 0);
v___x_2793_ = 0;
v___x_2794_ = lean_box(0);
lean_inc(v_mvarId_2792_);
v___x_2795_ = l_Lean_MVarId_refl(v_mvarId_2792_, v___x_2793_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2795_) == 0)
{
size_t v___x_2796_; size_t v___x_2797_; 
lean_dec_ref_known(v___x_2795_, 1);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2781_, v___x_2796_);
v_i_2781_ = v___x_2797_;
v_b_2782_ = v___x_2794_;
goto _start;
}
else
{
return v___x_2795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2799_, lean_object* v_sz_2800_, lean_object* v_i_2801_, lean_object* v_b_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
size_t v_sz_boxed_2808_; size_t v_i_boxed_2809_; lean_object* v_res_2810_; 
v_sz_boxed_2808_ = lean_unbox_usize(v_sz_2800_);
lean_dec(v_sz_2800_);
v_i_boxed_2809_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_res_2810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2799_, v_sz_boxed_2808_, v_i_boxed_2809_, v_b_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec_ref(v_as_2799_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2811_, lean_object* v_tail_2812_, lean_object* v_recName_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v_val_2825_, uint8_t v___x_2826_, lean_object* v_brecOnGoName_2827_, lean_object* v_levelParams_2828_, lean_object* v___x_2829_, lean_object* v_brecOnName_2830_, lean_object* v___x_2831_, lean_object* v_brecOnEqName_2832_, lean_object* v_fs_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; size_t v_sz_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
lean_inc(v___x_2811_);
v___x_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2811_);
lean_ctor_set(v___x_2839_, 1, v_tail_2812_);
v___x_2840_ = l_Lean_Expr_const___override(v_recName_2813_, v___x_2839_);
v___x_2841_ = l_Lean_mkAppN(v___x_2840_, v___x_2814_);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2815_);
v_sz_2843_ = lean_array_size(v___x_2816_);
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2817_, v___x_2818_, v___x_2816_, v_sz_2843_, v___x_2844_, v___x_2842_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v_fst_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_3212_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v_fst_2847_ = lean_ctor_get(v_a_2846_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v_a_2846_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v_a_2846_, 1);
lean_dec(v_unused_3213_);
v___x_2849_ = v_a_2846_;
v_isShared_2850_ = v_isSharedCheck_3212_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_fst_2847_);
lean_dec(v_a_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_3212_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
size_t v_sz_2851_; lean_object* v___x_2852_; 
v_sz_2851_ = lean_array_size(v___x_2819_);
lean_inc_ref(v_fs_2833_);
lean_inc_ref(v___x_2820_);
lean_inc_ref(v___x_2816_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2811_, v___x_2816_, v___x_2820_, v_fs_2833_, v___x_2819_, v_sz_2851_, v___x_2844_, v_fst_2847_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_mkAppN(v_a_2853_, v___x_2821_);
lean_inc_ref_n(v___x_2822_, 3);
v___x_2855_ = l_Lean_Expr_app___override(v___x_2854_, v___x_2822_);
v___x_2856_ = l_Array_append___redArg(v___x_2814_, v___x_2816_);
v___x_2857_ = l_Array_append___redArg(v___x_2856_, v___x_2821_);
v___x_2858_ = lean_mk_empty_array_with_capacity(v___x_2823_);
v___x_2859_ = lean_array_push(v___x_2858_, v___x_2822_);
v___x_2860_ = l_Array_append___redArg(v___x_2857_, v___x_2859_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = l_Array_append___redArg(v___x_2860_, v_fs_2833_);
v___x_2862_ = lean_array_get(v___x_2824_, v___x_2816_, v_val_2825_);
lean_dec_ref(v___x_2816_);
v___x_2863_ = lean_array_push(v___x_2821_, v___x_2822_);
v___x_2864_ = l_Lean_mkAppN(v___x_2862_, v___x_2863_);
v___x_2865_ = lean_array_get(v___x_2824_, v___x_2820_, v_val_2825_);
lean_dec_ref(v___x_2820_);
v___x_2866_ = l_Lean_mkAppN(v___x_2865_, v___x_2863_);
lean_inc_ref(v___x_2864_);
v___x_2867_ = l_Lean_Meta_mkPProd(v___x_2864_, v___x_2866_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = 0;
v___x_2870_ = 1;
v___x_2871_ = l_Lean_Meta_mkForallFVars(v___x_2861_, v_a_2868_, v___x_2869_, v___x_2826_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_Meta_mkLambdaFVars(v___x_2861_, v___x_2855_, v___x_2869_, v___x_2826_, v___x_2869_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_3179_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = lean_box(1);
lean_inc(v_levelParams_2828_);
lean_inc(v_brecOnGoName_2827_);
v___x_2876_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2827_, v_levelParams_2828_, v_a_2872_, v_a_2874_, v___x_2875_, v___y_2837_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_3179_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_3179_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
lean_inc(v_a_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set_tag(v___x_2879_, 1);
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_3178_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_addDecl(v___x_2882_, v___x_2869_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_toConstantVal_2884_; lean_object* v_name_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3175_; 
lean_dec_ref_known(v___x_2883_, 1);
v_toConstantVal_2884_ = lean_ctor_get(v_a_2877_, 0);
lean_inc_ref(v_toConstantVal_2884_);
lean_dec(v_a_2877_);
v_name_2885_ = lean_ctor_get(v_toConstantVal_2884_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_toConstantVal_2884_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; lean_object* v_unused_3177_; 
v_unused_3176_ = lean_ctor_get(v_toConstantVal_2884_, 2);
lean_dec(v_unused_3176_);
v_unused_3177_ = lean_ctor_get(v_toConstantVal_2884_, 1);
lean_dec(v_unused_3177_);
v___x_2887_ = v_toConstantVal_2884_;
v_isShared_2888_ = v_isSharedCheck_3175_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_name_2885_);
lean_dec(v_toConstantVal_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3175_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v_nextMacroScope_2892_; lean_object* v_ngen_2893_; lean_object* v_auxDeclNGen_2894_; lean_object* v_traceState_2895_; lean_object* v_recordedDeps_2896_; lean_object* v_messages_2897_; lean_object* v_infoState_2898_; lean_object* v_snapshotTasks_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_3173_; 
lean_inc(v_name_2885_);
v___x_2889_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2885_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___x_2889_);
v___x_2890_ = lean_st_ref_take(v___y_2837_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
v_nextMacroScope_2892_ = lean_ctor_get(v___x_2890_, 1);
v_ngen_2893_ = lean_ctor_get(v___x_2890_, 2);
v_auxDeclNGen_2894_ = lean_ctor_get(v___x_2890_, 3);
v_traceState_2895_ = lean_ctor_get(v___x_2890_, 4);
v_recordedDeps_2896_ = lean_ctor_get(v___x_2890_, 6);
v_messages_2897_ = lean_ctor_get(v___x_2890_, 7);
v_infoState_2898_ = lean_ctor_get(v___x_2890_, 8);
v_snapshotTasks_2899_ = lean_ctor_get(v___x_2890_, 9);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_2890_, 5);
lean_dec(v_unused_3174_);
v___x_2901_ = v___x_2890_;
v_isShared_2902_ = v_isSharedCheck_3173_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_snapshotTasks_2899_);
lean_inc(v_infoState_2898_);
lean_inc(v_messages_2897_);
lean_inc(v_recordedDeps_2896_);
lean_inc(v_traceState_2895_);
lean_inc(v_auxDeclNGen_2894_);
lean_inc(v_ngen_2893_);
lean_inc(v_nextMacroScope_2892_);
lean_inc(v_env_2891_);
lean_dec(v___x_2890_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_3173_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2903_ = l_Lean_addProtected(v_env_2891_, v_name_2885_);
v___x_2904_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 5, v___x_2904_);
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2906_ = v___x_2901_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_nextMacroScope_2892_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_ngen_2893_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_auxDeclNGen_2894_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_traceState_2895_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_recordedDeps_2896_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_messages_2897_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_infoState_2898_);
lean_ctor_set(v_reuseFailAlloc_3172_, 9, v_snapshotTasks_2899_);
v___x_2906_ = v_reuseFailAlloc_3172_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v_mctx_2909_; lean_object* v_zetaDeltaFVarIds_2910_; lean_object* v_postponed_2911_; lean_object* v_diag_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_3170_; 
v___x_2907_ = lean_st_ref_put(v___y_2837_, v___x_2906_);
v___x_2908_ = lean_st_ref_take(v___y_2835_);
v_mctx_2909_ = lean_ctor_get(v___x_2908_, 0);
v_zetaDeltaFVarIds_2910_ = lean_ctor_get(v___x_2908_, 2);
v_postponed_2911_ = lean_ctor_get(v___x_2908_, 3);
v_diag_2912_ = lean_ctor_get(v___x_2908_, 4);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v___x_2908_, 1);
lean_dec(v_unused_3171_);
v___x_2914_ = v___x_2908_;
v_isShared_2915_ = v_isSharedCheck_3170_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_diag_2912_);
lean_inc(v_postponed_2911_);
lean_inc(v_zetaDeltaFVarIds_2910_);
lean_inc(v_mctx_2909_);
lean_dec(v___x_2908_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_3170_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2916_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 1, v___x_2916_);
v___x_2918_ = v___x_2914_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_mctx_2909_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_zetaDeltaFVarIds_2910_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_postponed_2911_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_diag_2912_);
v___x_2918_ = v_reuseFailAlloc_3169_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2919_ = lean_st_ref_put(v___y_2835_, v___x_2918_);
lean_inc(v___x_2829_);
v___x_2920_ = l_Lean_Expr_const___override(v_brecOnGoName_2827_, v___x_2829_);
v___x_2921_ = l_Lean_mkAppN(v___x_2920_, v___x_2861_);
lean_inc_ref(v___x_2921_);
v___x_2922_ = l_Lean_Meta_mkPProdFstM(v___x_2921_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Meta_mkLambdaFVars(v___x_2861_, v_a_2923_, v___x_2869_, v___x_2826_, v___x_2869_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_mkForallFVars(v___x_2861_, v___x_2864_, v___x_2869_, v___x_2826_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_3144_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
lean_inc(v_levelParams_2828_);
v___x_2928_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2830_, v_levelParams_2828_, v_a_2927_, v_a_2925_, v___x_2875_, v___y_2837_);
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_2931_ = v___x_2928_;
v_isShared_2932_ = v_isSharedCheck_3144_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_3144_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
lean_inc(v_a_2929_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set_tag(v___x_2931_, 1);
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_3143_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_addDecl(v___x_2934_, v___x_2869_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_toConstantVal_2936_; lean_object* v_name_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref_known(v___x_2935_, 1);
v_toConstantVal_2936_ = lean_ctor_get(v_a_2929_, 0);
lean_inc_ref(v_toConstantVal_2936_);
lean_dec(v_a_2929_);
v_name_2937_ = lean_ctor_get(v_toConstantVal_2936_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_toConstantVal_2936_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; 
v_unused_3141_ = lean_ctor_get(v_toConstantVal_2936_, 2);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_toConstantVal_2936_, 1);
lean_dec(v_unused_3142_);
v___x_2939_ = v_toConstantVal_2936_;
v_isShared_2940_ = v_isSharedCheck_3140_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_name_2937_);
lean_dec(v_toConstantVal_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3140_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v_env_2943_; lean_object* v_nextMacroScope_2944_; lean_object* v_ngen_2945_; lean_object* v_auxDeclNGen_2946_; lean_object* v_traceState_2947_; lean_object* v_recordedDeps_2948_; lean_object* v_messages_2949_; lean_object* v_infoState_2950_; lean_object* v_snapshotTasks_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3138_; 
lean_inc(v_name_2937_);
v___x_2941_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2937_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___x_2941_);
v___x_2942_ = lean_st_ref_take(v___y_2837_);
v_env_2943_ = lean_ctor_get(v___x_2942_, 0);
v_nextMacroScope_2944_ = lean_ctor_get(v___x_2942_, 1);
v_ngen_2945_ = lean_ctor_get(v___x_2942_, 2);
v_auxDeclNGen_2946_ = lean_ctor_get(v___x_2942_, 3);
v_traceState_2947_ = lean_ctor_get(v___x_2942_, 4);
v_recordedDeps_2948_ = lean_ctor_get(v___x_2942_, 6);
v_messages_2949_ = lean_ctor_get(v___x_2942_, 7);
v_infoState_2950_ = lean_ctor_get(v___x_2942_, 8);
v_snapshotTasks_2951_ = lean_ctor_get(v___x_2942_, 9);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_2942_, 5);
lean_dec(v_unused_3139_);
v___x_2953_ = v___x_2942_;
v_isShared_2954_ = v_isSharedCheck_3138_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_snapshotTasks_2951_);
lean_inc(v_infoState_2950_);
lean_inc(v_messages_2949_);
lean_inc(v_recordedDeps_2948_);
lean_inc(v_traceState_2947_);
lean_inc(v_auxDeclNGen_2946_);
lean_inc(v_ngen_2945_);
lean_inc(v_nextMacroScope_2944_);
lean_inc(v_env_2943_);
lean_dec(v___x_2942_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3138_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_inc(v_name_2937_);
v___x_2955_ = l_Lean_markAuxRecursor(v_env_2943_, v_name_2937_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 5, v___x_2904_);
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2957_ = v___x_2953_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_nextMacroScope_2944_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_ngen_2945_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_auxDeclNGen_2946_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_traceState_2947_);
lean_ctor_set(v_reuseFailAlloc_3137_, 5, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_3137_, 6, v_recordedDeps_2948_);
lean_ctor_set(v_reuseFailAlloc_3137_, 7, v_messages_2949_);
lean_ctor_set(v_reuseFailAlloc_3137_, 8, v_infoState_2950_);
lean_ctor_set(v_reuseFailAlloc_3137_, 9, v_snapshotTasks_2951_);
v___x_2957_ = v_reuseFailAlloc_3137_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_mctx_2960_; lean_object* v_zetaDeltaFVarIds_2961_; lean_object* v_postponed_2962_; lean_object* v_diag_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3135_; 
v___x_2958_ = lean_st_ref_put(v___y_2837_, v___x_2957_);
v___x_2959_ = lean_st_ref_take(v___y_2835_);
v_mctx_2960_ = lean_ctor_get(v___x_2959_, 0);
v_zetaDeltaFVarIds_2961_ = lean_ctor_get(v___x_2959_, 2);
v_postponed_2962_ = lean_ctor_get(v___x_2959_, 3);
v_diag_2963_ = lean_ctor_get(v___x_2959_, 4);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___x_2959_, 1);
lean_dec(v_unused_3136_);
v___x_2965_ = v___x_2959_;
v_isShared_2966_ = v_isSharedCheck_3135_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_diag_2963_);
lean_inc(v_postponed_2962_);
lean_inc(v_zetaDeltaFVarIds_2961_);
lean_inc(v_mctx_2960_);
lean_dec(v___x_2959_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3135_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2916_);
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_mctx_2960_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_zetaDeltaFVarIds_2961_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_postponed_2962_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v_diag_2963_);
v___x_2968_ = v_reuseFailAlloc_3134_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_env_2971_; lean_object* v_nextMacroScope_2972_; lean_object* v_ngen_2973_; lean_object* v_auxDeclNGen_2974_; lean_object* v_traceState_2975_; lean_object* v_recordedDeps_2976_; lean_object* v_messages_2977_; lean_object* v_infoState_2978_; lean_object* v_snapshotTasks_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3132_; 
v___x_2969_ = lean_st_ref_put(v___y_2835_, v___x_2968_);
v___x_2970_ = lean_st_ref_take(v___y_2837_);
v_env_2971_ = lean_ctor_get(v___x_2970_, 0);
v_nextMacroScope_2972_ = lean_ctor_get(v___x_2970_, 1);
v_ngen_2973_ = lean_ctor_get(v___x_2970_, 2);
v_auxDeclNGen_2974_ = lean_ctor_get(v___x_2970_, 3);
v_traceState_2975_ = lean_ctor_get(v___x_2970_, 4);
v_recordedDeps_2976_ = lean_ctor_get(v___x_2970_, 6);
v_messages_2977_ = lean_ctor_get(v___x_2970_, 7);
v_infoState_2978_ = lean_ctor_get(v___x_2970_, 8);
v_snapshotTasks_2979_ = lean_ctor_get(v___x_2970_, 9);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_2970_, 5);
lean_dec(v_unused_3133_);
v___x_2981_ = v___x_2970_;
v_isShared_2982_ = v_isSharedCheck_3132_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_snapshotTasks_2979_);
lean_inc(v_infoState_2978_);
lean_inc(v_messages_2977_);
lean_inc(v_recordedDeps_2976_);
lean_inc(v_traceState_2975_);
lean_inc(v_auxDeclNGen_2974_);
lean_inc(v_ngen_2973_);
lean_inc(v_nextMacroScope_2972_);
lean_inc(v_env_2971_);
lean_dec(v___x_2970_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3132_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
lean_inc(v_name_2937_);
v___x_2983_ = l_Lean_addProtected(v_env_2971_, v_name_2937_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 5, v___x_2904_);
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_nextMacroScope_2972_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_ngen_2973_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_auxDeclNGen_2974_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_traceState_2975_);
lean_ctor_set(v_reuseFailAlloc_3131_, 5, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_3131_, 6, v_recordedDeps_2976_);
lean_ctor_set(v_reuseFailAlloc_3131_, 7, v_messages_2977_);
lean_ctor_set(v_reuseFailAlloc_3131_, 8, v_infoState_2978_);
lean_ctor_set(v_reuseFailAlloc_3131_, 9, v_snapshotTasks_2979_);
v___x_2985_ = v_reuseFailAlloc_3131_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v_mctx_2988_; lean_object* v_zetaDeltaFVarIds_2989_; lean_object* v_postponed_2990_; lean_object* v_diag_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3129_; 
v___x_2986_ = lean_st_ref_put(v___y_2837_, v___x_2985_);
v___x_2987_ = lean_st_ref_take(v___y_2835_);
v_mctx_2988_ = lean_ctor_get(v___x_2987_, 0);
v_zetaDeltaFVarIds_2989_ = lean_ctor_get(v___x_2987_, 2);
v_postponed_2990_ = lean_ctor_get(v___x_2987_, 3);
v_diag_2991_ = lean_ctor_get(v___x_2987_, 4);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v___x_2987_, 1);
lean_dec(v_unused_3130_);
v___x_2993_ = v___x_2987_;
v_isShared_2994_ = v_isSharedCheck_3129_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_diag_2991_);
lean_inc(v_postponed_2990_);
lean_inc(v_zetaDeltaFVarIds_2989_);
lean_inc(v_mctx_2988_);
lean_dec(v___x_2987_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3129_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 1, v___x_2916_);
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_mctx_2988_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_zetaDeltaFVarIds_2989_);
lean_ctor_set(v_reuseFailAlloc_3128_, 3, v_postponed_2990_);
lean_ctor_set(v_reuseFailAlloc_3128_, 4, v_diag_2991_);
v___x_2996_ = v_reuseFailAlloc_3128_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2997_ = lean_st_ref_put(v___y_2835_, v___x_2996_);
v___x_2998_ = l_Lean_Expr_const___override(v_name_2937_, v___x_2829_);
v___x_2999_ = l_Lean_mkAppN(v___x_2998_, v___x_2861_);
v___x_3000_ = lean_array_get(v___x_2824_, v_fs_2833_, v_val_2825_);
lean_dec_ref(v_fs_2833_);
v___x_3001_ = l_Lean_mkAppN(v___x_3000_, v___x_2863_);
lean_dec_ref(v___x_2863_);
v___x_3002_ = l_Lean_Meta_mkPProdSndM(v___x_2921_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = l_Lean_Expr_app___override(v___x_3001_, v_a_3003_);
v___x_3005_ = l_Lean_Meta_mkEq(v___x_2999_, v___x_3004_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc_n(v_a_3006_, 2);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = lean_box(0);
v___x_3008_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3006_, v___x_3007_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v___x_3010_ = l_Lean_Expr_mvarId_x21(v_a_3009_);
v___x_3011_ = l_Lean_Expr_fvarId_x21(v___x_2822_);
lean_dec_ref(v___x_2822_);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_2831_);
v___x_3013_ = lean_box(0);
v___x_3014_ = l_Lean_MVarId_cases(v___x_3010_, v___x_3011_, v___x_3012_, v___x_2869_, v___x_3013_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; size_t v_sz_3017_; lean_object* v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_box(0);
v_sz_3017_ = lean_array_size(v_a_3015_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3015_, v_sz_3017_, v___x_2844_, v___x_3016_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v_a_3015_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v_a_3020_; lean_object* v___x_3021_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3009_, v___y_2835_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = l_Lean_Meta_mkForallFVars(v___x_2861_, v_a_3006_, v___x_2869_, v___x_2826_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = l_Lean_Meta_mkLambdaFVars(v___x_2861_, v_a_3020_, v___x_2869_, v___x_2826_, v___x_2869_, v___x_2826_, v___x_2870_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___x_2861_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
lean_inc(v_brecOnEqName_2832_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 2, v_a_3022_);
lean_ctor_set(v___x_2939_, 1, v_levelParams_2828_);
lean_ctor_set(v___x_2939_, 0, v_brecOnEqName_2832_);
v___x_3026_ = v___x_2939_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_brecOnEqName_2832_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_levelParams_2828_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_a_3022_);
v___x_3026_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___x_3027_ = lean_box(0);
lean_inc(v_brecOnEqName_2832_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set_tag(v___x_2849_, 1);
lean_ctor_set(v___x_2849_, 1, v___x_3027_);
lean_ctor_set(v___x_2849_, 0, v_brecOnEqName_2832_);
v___x_3029_ = v___x_2849_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_brecOnEqName_2832_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 2, v___x_3029_);
lean_ctor_set(v___x_2887_, 1, v_a_3024_);
lean_ctor_set(v___x_2887_, 0, v___x_3026_);
v___x_3031_ = v___x_2887_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_a_3024_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v_a_3033_; lean_object* v___x_3034_; 
v___x_3032_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3031_, v___y_2837_);
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref(v___x_3032_);
v___x_3034_ = l_Lean_addDecl(v_a_3033_, v___x_2869_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3075_; 
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3075_ == 0)
{
lean_object* v_unused_3076_; 
v_unused_3076_ = lean_ctor_get(v___x_3034_, 0);
lean_dec(v_unused_3076_);
v___x_3036_ = v___x_3034_;
v_isShared_3037_ = v_isSharedCheck_3075_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3034_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3075_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v_env_3039_; lean_object* v_nextMacroScope_3040_; lean_object* v_ngen_3041_; lean_object* v_auxDeclNGen_3042_; lean_object* v_traceState_3043_; lean_object* v_recordedDeps_3044_; lean_object* v_messages_3045_; lean_object* v_infoState_3046_; lean_object* v_snapshotTasks_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3073_; 
v___x_3038_ = lean_st_ref_take(v___y_2837_);
v_env_3039_ = lean_ctor_get(v___x_3038_, 0);
v_nextMacroScope_3040_ = lean_ctor_get(v___x_3038_, 1);
v_ngen_3041_ = lean_ctor_get(v___x_3038_, 2);
v_auxDeclNGen_3042_ = lean_ctor_get(v___x_3038_, 3);
v_traceState_3043_ = lean_ctor_get(v___x_3038_, 4);
v_recordedDeps_3044_ = lean_ctor_get(v___x_3038_, 6);
v_messages_3045_ = lean_ctor_get(v___x_3038_, 7);
v_infoState_3046_ = lean_ctor_get(v___x_3038_, 8);
v_snapshotTasks_3047_ = lean_ctor_get(v___x_3038_, 9);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3038_, 5);
lean_dec(v_unused_3074_);
v___x_3049_ = v___x_3038_;
v_isShared_3050_ = v_isSharedCheck_3073_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_snapshotTasks_3047_);
lean_inc(v_infoState_3046_);
lean_inc(v_messages_3045_);
lean_inc(v_recordedDeps_3044_);
lean_inc(v_traceState_3043_);
lean_inc(v_auxDeclNGen_3042_);
lean_inc(v_ngen_3041_);
lean_inc(v_nextMacroScope_3040_);
lean_inc(v_env_3039_);
lean_dec(v___x_3038_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3073_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3051_ = l_Lean_addProtected(v_env_3039_, v_brecOnEqName_2832_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 5, v___x_2904_);
lean_ctor_set(v___x_3049_, 0, v___x_3051_);
v___x_3053_ = v___x_3049_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v_nextMacroScope_3040_);
lean_ctor_set(v_reuseFailAlloc_3072_, 2, v_ngen_3041_);
lean_ctor_set(v_reuseFailAlloc_3072_, 3, v_auxDeclNGen_3042_);
lean_ctor_set(v_reuseFailAlloc_3072_, 4, v_traceState_3043_);
lean_ctor_set(v_reuseFailAlloc_3072_, 5, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_3072_, 6, v_recordedDeps_3044_);
lean_ctor_set(v_reuseFailAlloc_3072_, 7, v_messages_3045_);
lean_ctor_set(v_reuseFailAlloc_3072_, 8, v_infoState_3046_);
lean_ctor_set(v_reuseFailAlloc_3072_, 9, v_snapshotTasks_3047_);
v___x_3053_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_mctx_3056_; lean_object* v_zetaDeltaFVarIds_3057_; lean_object* v_postponed_3058_; lean_object* v_diag_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3070_; 
v___x_3054_ = lean_st_ref_put(v___y_2837_, v___x_3053_);
v___x_3055_ = lean_st_ref_take(v___y_2835_);
v_mctx_3056_ = lean_ctor_get(v___x_3055_, 0);
v_zetaDeltaFVarIds_3057_ = lean_ctor_get(v___x_3055_, 2);
v_postponed_3058_ = lean_ctor_get(v___x_3055_, 3);
v_diag_3059_ = lean_ctor_get(v___x_3055_, 4);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_3055_, 1);
lean_dec(v_unused_3071_);
v___x_3061_ = v___x_3055_;
v_isShared_3062_ = v_isSharedCheck_3070_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_diag_3059_);
lean_inc(v_postponed_3058_);
lean_inc(v_zetaDeltaFVarIds_3057_);
lean_inc(v_mctx_3056_);
lean_dec(v___x_3055_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3070_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 1, v___x_2916_);
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_mctx_3056_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_3069_, 2, v_zetaDeltaFVarIds_3057_);
lean_ctor_set(v_reuseFailAlloc_3069_, 3, v_postponed_3058_);
lean_ctor_set(v_reuseFailAlloc_3069_, 4, v_diag_3059_);
v___x_3064_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3065_ = lean_st_ref_put(v___y_2835_, v___x_3064_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3016_);
v___x_3067_ = v___x_3036_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3016_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2832_);
return v___x_3034_;
}
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_3022_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
v_a_3080_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3023_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3023_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_a_3020_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
v_a_3088_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3021_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3021_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_dec(v_a_3009_);
lean_dec(v_a_3006_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
return v___x_3018_;
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3009_);
lean_dec(v_a_3006_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
v_a_3096_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3014_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3014_);
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
lean_dec(v_a_3006_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3104_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3008_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3008_);
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
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3112_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3005_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3005_);
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
lean_dec_ref(v___x_3001_);
lean_dec_ref(v___x_2999_);
lean_del_object(v___x_2939_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3120_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3002_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3002_);
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
lean_dec(v_a_2929_);
lean_dec_ref(v___x_2921_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec(v_a_2925_);
lean_dec_ref(v___x_2921_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3145_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_2926_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_2926_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___x_2921_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3153_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_2924_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_2924_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref(v___x_2921_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec_ref(v___x_2822_);
v_a_3161_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_2922_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_2922_);
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
}
}
}
}
}
else
{
lean_dec(v_a_2877_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_2872_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
v_a_3180_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_2873_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_2873_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2855_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
v_a_3188_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_2871_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_2871_);
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
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2863_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2855_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
v_a_3196_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_2867_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_2867_);
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
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v___x_2814_);
v_a_3204_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_2852_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_2852_);
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
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v_fs_2833_);
lean_dec(v_brecOnEqName_2832_);
lean_dec(v_brecOnName_2830_);
lean_dec(v___x_2829_);
lean_dec(v_levelParams_2828_);
lean_dec(v_brecOnGoName_2827_);
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2821_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v___x_2814_);
lean_dec(v___x_2811_);
v_a_3214_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_2845_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_2845_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3222_ = _args[0];
lean_object* v_tail_3223_ = _args[1];
lean_object* v_recName_3224_ = _args[2];
lean_object* v___x_3225_ = _args[3];
lean_object* v___x_3226_ = _args[4];
lean_object* v___x_3227_ = _args[5];
lean_object* v___x_3228_ = _args[6];
lean_object* v___x_3229_ = _args[7];
lean_object* v___x_3230_ = _args[8];
lean_object* v___x_3231_ = _args[9];
lean_object* v___x_3232_ = _args[10];
lean_object* v___x_3233_ = _args[11];
lean_object* v___x_3234_ = _args[12];
lean_object* v___x_3235_ = _args[13];
lean_object* v_val_3236_ = _args[14];
lean_object* v___x_3237_ = _args[15];
lean_object* v_brecOnGoName_3238_ = _args[16];
lean_object* v_levelParams_3239_ = _args[17];
lean_object* v___x_3240_ = _args[18];
lean_object* v_brecOnName_3241_ = _args[19];
lean_object* v___x_3242_ = _args[20];
lean_object* v_brecOnEqName_3243_ = _args[21];
lean_object* v_fs_3244_ = _args[22];
lean_object* v___y_3245_ = _args[23];
lean_object* v___y_3246_ = _args[24];
lean_object* v___y_3247_ = _args[25];
lean_object* v___y_3248_ = _args[26];
lean_object* v___y_3249_ = _args[27];
_start:
{
uint8_t v___x_31458__boxed_3250_; lean_object* v_res_3251_; 
v___x_31458__boxed_3250_ = lean_unbox(v___x_3237_);
v_res_3251_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3222_, v_tail_3223_, v_recName_3224_, v___x_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v___x_3231_, v___x_3232_, v___x_3233_, v___x_3234_, v___x_3235_, v_val_3236_, v___x_31458__boxed_3250_, v_brecOnGoName_3238_, v_levelParams_3239_, v___x_3240_, v_brecOnName_3241_, v___x_3242_, v_brecOnEqName_3243_, v_fs_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___x_3242_);
lean_dec(v_val_3236_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3234_);
lean_dec_ref(v___x_3230_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3252_, lean_object* v_a_3253_, uint8_t v___x_3254_, lean_object* v_f_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; uint8_t v___x_3264_; lean_object* v___x_3265_; 
lean_inc_ref(v_targs_3252_);
v___x_3261_ = lean_array_push(v_targs_3252_, v_f_3255_);
v___x_3262_ = l_Lean_mkAppN(v_a_3253_, v_targs_3252_);
lean_dec_ref(v_targs_3252_);
v___x_3263_ = 0;
v___x_3264_ = 1;
v___x_3265_ = l_Lean_Meta_mkForallFVars(v___x_3261_, v___x_3262_, v___x_3263_, v___x_3254_, v___x_3254_, v___x_3264_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec_ref(v___x_3261_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3266_, lean_object* v_a_3267_, lean_object* v___x_3268_, lean_object* v_f_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v___x_32172__boxed_3275_; lean_object* v_res_3276_; 
v___x_32172__boxed_3275_ = lean_unbox(v___x_3268_);
v_res_3276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3266_, v_a_3267_, v___x_32172__boxed_3275_, v_f_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3280_, uint8_t v___x_3281_, lean_object* v___x_3282_, lean_object* v_targs_3283_, lean_object* v_x_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v___x_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3290_ = lean_box(v___x_3281_);
lean_inc_ref(v_targs_3283_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3291_, 0, v_targs_3283_);
lean_closure_set(v___f_3291_, 1, v_a_3280_);
lean_closure_set(v___f_3291_, 2, v___x_3290_);
v___x_3292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3293_ = l_Lean_mkAppN(v___x_3282_, v_targs_3283_);
lean_dec_ref(v_targs_3283_);
v___x_3294_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3292_, v___x_3293_, v___f_3291_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3295_, lean_object* v___x_3296_, lean_object* v___x_3297_, lean_object* v_targs_3298_, lean_object* v_x_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v___x_32206__boxed_3305_; lean_object* v_res_3306_; 
v___x_32206__boxed_3305_ = lean_unbox(v___x_3296_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3295_, v___x_32206__boxed_3305_, v___x_3297_, v_targs_3298_, v_x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec_ref(v_x_3299_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3314_, 0, v_a_3307_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3315_, lean_object* v_x_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3315_, v_x_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec_ref(v_x_3316_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_as_3326_, size_t v_sz_3327_, size_t v_i_3328_, lean_object* v_b_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_lt(v_i_3328_, v_sz_3327_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_b_3329_);
return v___x_3336_;
}
else
{
lean_object* v_snd_3337_; lean_object* v_fst_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3435_; 
v_snd_3337_ = lean_ctor_get(v_b_3329_, 1);
v_fst_3338_ = lean_ctor_get(v_b_3329_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_b_3329_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3340_ = v_b_3329_;
v_isShared_3341_ = v_isSharedCheck_3435_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_snd_3337_);
lean_inc(v_fst_3338_);
lean_dec(v_b_3329_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3435_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v_fst_3342_; lean_object* v_snd_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3434_; 
v_fst_3342_ = lean_ctor_get(v_snd_3337_, 0);
v_snd_3343_ = lean_ctor_get(v_snd_3337_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_snd_3337_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3345_ = v_snd_3337_;
v_isShared_3346_ = v_isSharedCheck_3434_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3343_);
lean_inc(v_fst_3342_);
lean_dec(v_snd_3337_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3434_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_next_3355_; 
v_next_3355_ = lean_ctor_get(v_snd_3343_, 0);
lean_inc(v_next_3355_);
if (lean_obj_tag(v_next_3355_) == 0)
{
goto v___jp_3347_;
}
else
{
lean_object* v_upperBound_3356_; lean_object* v_val_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3433_; 
v_upperBound_3356_ = lean_ctor_get(v_snd_3343_, 1);
v_val_3357_ = lean_ctor_get(v_next_3355_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_next_3355_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3359_ = v_next_3355_;
v_isShared_3360_ = v_isSharedCheck_3433_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_val_3357_);
lean_dec(v_next_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3433_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_nat_dec_lt(v_val_3357_, v_upperBound_3356_);
if (v___x_3361_ == 0)
{
lean_del_object(v___x_3359_);
lean_dec(v_val_3357_);
goto v___jp_3347_;
}
else
{
lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3430_; 
lean_inc(v_upperBound_3356_);
lean_del_object(v___x_3345_);
lean_del_object(v___x_3340_);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_snd_3343_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; lean_object* v_unused_3432_; 
v_unused_3431_ = lean_ctor_get(v_snd_3343_, 1);
lean_dec(v_unused_3431_);
v_unused_3432_ = lean_ctor_get(v_snd_3343_, 0);
lean_dec(v_unused_3432_);
v___x_3363_ = v_snd_3343_;
v_isShared_3364_ = v_isSharedCheck_3430_;
goto v_resetjp_3362_;
}
else
{
lean_dec(v_snd_3343_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3430_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v_array_3365_; lean_object* v_start_3366_; lean_object* v_stop_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v_array_3365_ = lean_ctor_get(v_fst_3342_, 0);
v_start_3366_ = lean_ctor_get(v_fst_3342_, 1);
v_stop_3367_ = lean_ctor_get(v_fst_3342_, 2);
v___x_3368_ = lean_unsigned_to_nat(1u);
v___x_3369_ = lean_nat_add(v_val_3357_, v___x_3368_);
lean_dec(v_val_3357_);
lean_inc(v___x_3369_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3369_);
v___x_3371_ = v___x_3359_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3373_; 
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3371_);
v___x_3373_ = v___x_3363_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3371_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_upperBound_3356_);
v___x_3373_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
uint8_t v___x_3374_; 
v___x_3374_ = lean_nat_dec_lt(v_start_3366_, v_stop_3367_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
lean_dec(v___x_3369_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v_fst_3342_);
lean_ctor_set(v___x_3375_, 1, v___x_3373_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_fst_3338_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
else
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3424_; 
lean_inc(v_stop_3367_);
lean_inc(v_start_3366_);
lean_inc_ref(v_array_3365_);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_fst_3342_);
if (v_isSharedCheck_3424_ == 0)
{
lean_object* v_unused_3425_; lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3425_ = lean_ctor_get(v_fst_3342_, 2);
lean_dec(v_unused_3425_);
v_unused_3426_ = lean_ctor_get(v_fst_3342_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_fst_3342_, 0);
lean_dec(v_unused_3427_);
v___x_3379_ = v_fst_3342_;
v_isShared_3380_ = v_isSharedCheck_3424_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_fst_3342_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3424_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
uint8_t v___x_3381_; lean_object* v_a_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3381_ = lean_nat_dec_lt(v___x_3324_, v___x_3325_);
v_a_3382_ = lean_array_uget_borrowed(v_as_3326_, v_i_3328_);
v___x_3383_ = lean_array_fget_borrowed(v_array_3365_, v_start_3366_);
v___x_3384_ = lean_box(v___x_3381_);
lean_inc(v___x_3383_);
lean_inc(v_a_3382_);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3385_, 0, v_a_3382_);
lean_closure_set(v___f_3385_, 1, v___x_3384_);
lean_closure_set(v___f_3385_, 2, v___x_3383_);
v___x_3386_ = lean_nat_add(v_start_3366_, v___x_3368_);
lean_dec(v_start_3366_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v___x_3386_);
v___x_3388_ = v___x_3379_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_array_3365_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3423_, 2, v_stop_3367_);
v___x_3388_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; 
lean_inc(v___y_3333_);
lean_inc_ref(v___y_3332_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v_a_3382_);
v___x_3389_ = lean_infer_type(v_a_3382_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = 0;
v___x_3392_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3390_, v___f_3385_, v___x_3391_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___f_3394_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3394_, 0, v_a_3393_);
v___x_3395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3396_ = l_Nat_reprFast(v___x_3369_);
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = lean_box(0);
v___x_3399_ = l_Lean_Name_str___override(v___x_3398_, v___x_3397_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v___f_3394_);
v___x_3401_ = lean_array_push(v_fst_3338_, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3388_);
lean_ctor_set(v___x_3402_, 1, v___x_3373_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = ((size_t)1ULL);
v___x_3405_ = lean_usize_add(v_i_3328_, v___x_3404_);
v_i_3328_ = v___x_3405_;
v_b_3329_ = v___x_3403_;
goto _start;
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___x_3388_);
lean_dec_ref(v___x_3373_);
lean_dec(v___x_3369_);
lean_dec(v_fst_3338_);
v_a_3407_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3392_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3392_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___x_3388_);
lean_dec_ref(v___f_3385_);
lean_dec_ref(v___x_3373_);
lean_dec(v___x_3369_);
lean_dec(v_fst_3338_);
v_a_3415_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3389_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3389_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
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
v___jp_3347_:
{
lean_object* v___x_3349_; 
if (v_isShared_3346_ == 0)
{
v___x_3349_ = v___x_3345_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_fst_3342_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_snd_3343_);
v___x_3349_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3341_ == 0)
{
lean_ctor_set(v___x_3340_, 1, v___x_3349_);
v___x_3351_ = v___x_3340_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_fst_3338_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3436_, lean_object* v___x_3437_, lean_object* v_as_3438_, lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
size_t v_sz_boxed_3447_; size_t v_i_boxed_3448_; lean_object* v_res_3449_; 
v_sz_boxed_3447_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3448_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3436_, v___x_3437_, v_as_3438_, v_sz_boxed_3447_, v_i_boxed_3448_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec_ref(v_as_3438_);
lean_dec(v___x_3437_);
lean_dec(v___x_3436_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3450_, size_t v_i_3451_, lean_object* v_bs_3452_){
_start:
{
uint8_t v___x_3453_; 
v___x_3453_ = lean_usize_dec_lt(v_i_3451_, v_sz_3450_);
if (v___x_3453_ == 0)
{
return v_bs_3452_;
}
else
{
lean_object* v_v_3454_; lean_object* v_fst_3455_; lean_object* v_snd_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3472_; 
v_v_3454_ = lean_array_uget(v_bs_3452_, v_i_3451_);
v_fst_3455_ = lean_ctor_get(v_v_3454_, 0);
v_snd_3456_ = lean_ctor_get(v_v_3454_, 1);
v_isSharedCheck_3472_ = !lean_is_exclusive(v_v_3454_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3458_ = v_v_3454_;
v_isShared_3459_ = v_isSharedCheck_3472_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_snd_3456_);
lean_inc(v_fst_3455_);
lean_dec(v_v_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3472_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_bs_x27_3461_; uint8_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3460_ = lean_unsigned_to_nat(0u);
v_bs_x27_3461_ = lean_array_uset(v_bs_3452_, v_i_3451_, v___x_3460_);
v___x_3462_ = 0;
v___x_3463_ = lean_box(v___x_3462_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3463_);
v___x_3465_ = v___x_3458_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3463_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_snd_3456_);
v___x_3465_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; size_t v___x_3467_; size_t v___x_3468_; lean_object* v___x_3469_; 
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v_fst_3455_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = ((size_t)1ULL);
v___x_3468_ = lean_usize_add(v_i_3451_, v___x_3467_);
v___x_3469_ = lean_array_uset(v_bs_x27_3461_, v_i_3451_, v___x_3466_);
v_i_3451_ = v___x_3468_;
v_bs_3452_ = v___x_3469_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3473_, lean_object* v_i_3474_, lean_object* v_bs_3475_){
_start:
{
size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3473_);
lean_dec(v_sz_3473_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3474_);
lean_dec(v_i_3474_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3476_, v_i_boxed_3477_, v_bs_3475_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3479_, lean_object* v___x_3480_, lean_object* v_a_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_31002__overap_3487_; lean_object* v___x_3488_; 
v___x_31002__overap_3487_ = l_instInhabitedOfMonad___redArg(v___x_3479_, v___x_3480_);
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
v___x_3488_ = lean_apply_5(v___x_31002__overap_3487_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, lean_box(0));
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3489_, lean_object* v___x_3490_, lean_object* v_a_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3489_, v___x_3490_, v_a_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec_ref(v_a_3491_);
return v_res_3497_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_instMonadEIO___redArg();
return v___x_3498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3500_ = l_StateRefT_x27_instMonad___redArg(v___x_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3505_, lean_object* v_declInfos_3506_, lean_object* v_k_3507_, lean_object* v_kind_3508_, lean_object* v_b_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v_kind_boxed_3515_; lean_object* v_res_3516_; 
v_kind_boxed_3515_ = lean_unbox(v_kind_3508_);
v_res_3516_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3505_, v_declInfos_3506_, v_k_3507_, v_kind_boxed_3515_, v_b_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3517_, lean_object* v_declInfos_3518_, lean_object* v_k_3519_, uint8_t v_kind_3520_, lean_object* v_name_3521_, uint8_t v_bi_3522_, lean_object* v_type_3523_, uint8_t v_kind_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v___f_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_box(v_kind_3520_);
v___f_3531_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3531_, 0, v_acc_3517_);
lean_closure_set(v___f_3531_, 1, v_declInfos_3518_);
lean_closure_set(v___f_3531_, 2, v_k_3519_);
lean_closure_set(v___f_3531_, 3, v___x_3530_);
v___x_3532_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3521_, v_bi_3522_, v_type_3523_, v___f_3531_, v_kind_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
v_a_3541_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3549_, lean_object* v_k_3550_, uint8_t v_kind_3551_, lean_object* v_acc_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; lean_object* v_toApplicative_3559_; lean_object* v_toFunctor_3560_; lean_object* v_toSeq_3561_; lean_object* v_toSeqLeft_3562_; lean_object* v_toSeqRight_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___f_3566_; lean_object* v___f_3567_; lean_object* v___x_3568_; lean_object* v___f_3569_; lean_object* v___f_3570_; lean_object* v___f_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v_toApplicative_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3631_; 
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3559_ = lean_ctor_get(v___x_3558_, 0);
v_toFunctor_3560_ = lean_ctor_get(v_toApplicative_3559_, 0);
v_toSeq_3561_ = lean_ctor_get(v_toApplicative_3559_, 2);
v_toSeqLeft_3562_ = lean_ctor_get(v_toApplicative_3559_, 3);
v_toSeqRight_3563_ = lean_ctor_get(v_toApplicative_3559_, 4);
v___f_3564_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3565_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3560_, 2);
v___f_3566_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3566_, 0, v_toFunctor_3560_);
v___f_3567_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3567_, 0, v_toFunctor_3560_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___f_3566_);
lean_ctor_set(v___x_3568_, 1, v___f_3567_);
lean_inc(v_toSeqRight_3563_);
v___f_3569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3569_, 0, v_toSeqRight_3563_);
lean_inc(v_toSeqLeft_3562_);
v___f_3570_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3570_, 0, v_toSeqLeft_3562_);
lean_inc(v_toSeq_3561_);
v___f_3571_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3571_, 0, v_toSeq_3561_);
v___x_3572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3568_);
lean_ctor_set(v___x_3572_, 1, v___f_3564_);
lean_ctor_set(v___x_3572_, 2, v___f_3571_);
lean_ctor_set(v___x_3572_, 3, v___f_3570_);
lean_ctor_set(v___x_3572_, 4, v___f_3569_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___f_3565_);
v___x_3574_ = l_StateRefT_x27_instMonad___redArg(v___x_3573_);
v_toApplicative_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v___x_3574_, 1);
lean_dec(v_unused_3632_);
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3631_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_toApplicative_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3631_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v_toFunctor_3579_; lean_object* v_toSeq_3580_; lean_object* v_toSeqLeft_3581_; lean_object* v_toSeqRight_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3629_; 
v_toFunctor_3579_ = lean_ctor_get(v_toApplicative_3575_, 0);
v_toSeq_3580_ = lean_ctor_get(v_toApplicative_3575_, 2);
v_toSeqLeft_3581_ = lean_ctor_get(v_toApplicative_3575_, 3);
v_toSeqRight_3582_ = lean_ctor_get(v_toApplicative_3575_, 4);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_toApplicative_3575_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_toApplicative_3575_, 1);
lean_dec(v_unused_3630_);
v___x_3584_ = v_toApplicative_3575_;
v_isShared_3585_ = v_isSharedCheck_3629_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_toSeqRight_3582_);
lean_inc(v_toSeqLeft_3581_);
lean_inc(v_toSeq_3580_);
lean_inc(v_toFunctor_3579_);
lean_dec(v_toApplicative_3575_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3629_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___x_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3595_; 
v___f_3586_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3587_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3579_);
v___f_3588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3588_, 0, v_toFunctor_3579_);
v___f_3589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3589_, 0, v_toFunctor_3579_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___f_3588_);
lean_ctor_set(v___x_3590_, 1, v___f_3589_);
v___f_3591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3591_, 0, v_toSeqRight_3582_);
v___f_3592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3592_, 0, v_toSeqLeft_3581_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toSeq_3580_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___f_3591_);
lean_ctor_set(v___x_3584_, 3, v___f_3592_);
lean_ctor_set(v___x_3584_, 2, v___f_3593_);
lean_ctor_set(v___x_3584_, 1, v___f_3586_);
lean_ctor_set(v___x_3584_, 0, v___x_3590_);
v___x_3595_ = v___x_3584_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___f_3586_);
lean_ctor_set(v_reuseFailAlloc_3628_, 2, v___f_3593_);
lean_ctor_set(v_reuseFailAlloc_3628_, 3, v___f_3592_);
lean_ctor_set(v_reuseFailAlloc_3628_, 4, v___f_3591_);
v___x_3595_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3597_; 
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 1, v___f_3587_);
lean_ctor_set(v___x_3577_, 0, v___x_3595_);
v___x_3597_ = v___x_3577_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3627_, 1, v___f_3587_);
v___x_3597_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3598_ = lean_array_get_size(v_acc_3552_);
v___x_3599_ = lean_array_get_size(v_declInfos_3549_);
v___x_3600_ = lean_nat_dec_lt(v___x_3598_, v___x_3599_);
if (v___x_3600_ == 0)
{
lean_object* v___x_3601_; 
lean_dec_ref(v___x_3597_);
lean_dec_ref(v_declInfos_3549_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3553_);
v___x_3601_ = lean_apply_6(v_k_3550_, v_acc_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, lean_box(0));
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___f_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v_snd_3611_; lean_object* v_fst_3612_; lean_object* v_fst_3613_; lean_object* v_snd_3614_; lean_object* v___x_3615_; 
v___x_3602_ = lean_box(0);
v___x_3603_ = 0;
v___x_3604_ = l_Lean_instInhabitedExpr;
v___f_3605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3605_, 0, v___x_3597_);
lean_closure_set(v___f_3605_, 1, v___x_3604_);
v___f_3606_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3606_, 0, v___f_3605_);
v___x_3607_ = lean_box(v___x_3603_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___f_3606_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3602_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_array_get(v___x_3609_, v_declInfos_3549_, v___x_3598_);
lean_dec_ref_known(v___x_3609_, 2);
v_snd_3611_ = lean_ctor_get(v___x_3610_, 1);
lean_inc(v_snd_3611_);
v_fst_3612_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_fst_3612_);
lean_dec(v___x_3610_);
v_fst_3613_ = lean_ctor_get(v_snd_3611_, 0);
lean_inc(v_fst_3613_);
v_snd_3614_ = lean_ctor_get(v_snd_3611_, 1);
lean_inc(v_snd_3614_);
lean_dec(v_snd_3611_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3553_);
lean_inc_ref(v_acc_3552_);
v___x_3615_ = lean_apply_6(v_snd_3614_, v_acc_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, lean_box(0));
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = lean_unbox(v_fst_3613_);
lean_dec(v_fst_3613_);
v___x_3618_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3552_, v_declInfos_3549_, v_k_3550_, v_kind_3551_, v_fst_3612_, v___x_3617_, v_a_3616_, v_kind_3551_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3618_;
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec(v_fst_3613_);
lean_dec(v_fst_3612_);
lean_dec_ref(v_acc_3552_);
lean_dec_ref(v_k_3550_);
lean_dec_ref(v_declInfos_3549_);
v_a_3619_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3615_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3615_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3633_, lean_object* v_declInfos_3634_, lean_object* v_k_3635_, uint8_t v_kind_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_array_push(v_acc_3633_, v_b_3637_);
v___x_3644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3634_, v_k_3635_, v_kind_3636_, v___x_3643_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
return v___x_3644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3645_, lean_object* v_declInfos_3646_, lean_object* v_k_3647_, lean_object* v_kind_3648_, lean_object* v_name_3649_, lean_object* v_bi_3650_, lean_object* v_type_3651_, lean_object* v_kind_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v_kind_boxed_3658_; uint8_t v_bi_boxed_3659_; uint8_t v_kind_boxed_3660_; lean_object* v_res_3661_; 
v_kind_boxed_3658_ = lean_unbox(v_kind_3648_);
v_bi_boxed_3659_ = lean_unbox(v_bi_3650_);
v_kind_boxed_3660_ = lean_unbox(v_kind_3652_);
v_res_3661_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3645_, v_declInfos_3646_, v_k_3647_, v_kind_boxed_3658_, v_name_3649_, v_bi_boxed_3659_, v_type_3651_, v_kind_boxed_3660_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3662_, lean_object* v_k_3663_, lean_object* v_kind_3664_, lean_object* v_acc_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
uint8_t v_kind_boxed_3671_; lean_object* v_res_3672_; 
v_kind_boxed_3671_ = lean_unbox(v_kind_3664_);
v_res_3672_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3662_, v_k_3663_, v_kind_boxed_3671_, v_acc_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec_ref(v___y_3668_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3673_, lean_object* v_k_3674_, uint8_t v_kind_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3673_, v_k_3674_, v_kind_3675_, v___x_3681_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3683_, lean_object* v_k_3684_, lean_object* v_kind_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
uint8_t v_kind_boxed_3691_; lean_object* v_res_3692_; 
v_kind_boxed_3691_ = lean_unbox(v_kind_3685_);
v_res_3692_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3683_, v_k_3684_, v_kind_boxed_3691_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3693_, lean_object* v_k_3694_, uint8_t v_kind_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
size_t v_sz_3701_; size_t v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; 
v_sz_3701_ = lean_array_size(v_declInfos_3693_);
v___x_3702_ = ((size_t)0ULL);
v___x_3703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3701_, v___x_3702_, v_declInfos_3693_);
v___x_3704_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3703_, v_k_3694_, v_kind_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3705_, lean_object* v_k_3706_, lean_object* v_kind_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
uint8_t v_kind_boxed_3713_; lean_object* v_res_3714_; 
v_kind_boxed_3713_ = lean_unbox(v_kind_3707_);
v_res_3714_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3705_, v_k_3706_, v_kind_boxed_3713_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
return v_res_3714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3716_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3717_ = lean_unsigned_to_nat(4u);
v___x_3718_ = lean_unsigned_to_nat(202u);
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3720_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3721_ = l_mkPanicMessageWithDecl(v___x_3720_, v___x_3719_, v___x_3718_, v___x_3717_, v___x_3716_);
return v___x_3721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3732_, lean_object* v_numMotives_3733_, lean_object* v_numMinors_3734_, lean_object* v___x_3735_, lean_object* v_all_3736_, lean_object* v___x_3737_, lean_object* v___x_3738_, lean_object* v_head_3739_, lean_object* v_tail_3740_, lean_object* v_recName_3741_, lean_object* v_brecOnGoName_3742_, lean_object* v_levelParams_3743_, lean_object* v_brecOnName_3744_, lean_object* v_brecOnEqName_3745_, lean_object* v_type_3746_, lean_object* v_refArgs_3747_, lean_object* v_refBody_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3754_ = lean_nat_add(v_nParams_3732_, v_numMotives_3733_);
v___x_3755_ = lean_nat_add(v___x_3754_, v_numMinors_3734_);
v___x_3756_ = lean_array_get_size(v_refArgs_3747_);
v___x_3757_ = lean_nat_dec_lt(v___x_3755_, v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
lean_dec(v___x_3755_);
lean_dec(v___x_3754_);
lean_dec_ref(v_refArgs_3747_);
lean_dec_ref(v_type_3746_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3737_);
lean_dec_ref(v_all_3736_);
lean_dec(v___x_3735_);
lean_dec(v_nParams_3732_);
v___x_3758_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3759_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3758_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3759_;
}
else
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3760_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3732_);
lean_inc_ref_n(v_refArgs_3747_, 2);
v___x_3761_ = l_Array_toSubarray___redArg(v_refArgs_3747_, v___x_3760_, v_nParams_3732_);
lean_inc(v___x_3754_);
v___x_3762_ = l_Array_toSubarray___redArg(v_refArgs_3747_, v_nParams_3732_, v___x_3754_);
v___x_3763_ = l_Subarray_copy___redArg(v___x_3762_);
v___x_3764_ = l_Lean_Expr_getAppFn(v_refBody_3748_);
v___x_3765_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3763_, v___x_3764_);
lean_dec_ref(v___x_3764_);
if (lean_obj_tag(v___x_3765_) == 1)
{
lean_object* v_val_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___f_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec_ref(v_type_3746_);
v_val_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_val_3766_);
lean_dec_ref_known(v___x_3765_, 1);
lean_inc_n(v___x_3755_, 2);
lean_inc_ref_n(v_refArgs_3747_, 2);
v___x_3767_ = l_Array_toSubarray___redArg(v_refArgs_3747_, v___x_3754_, v___x_3755_);
v___x_3768_ = l_Subarray_copy___redArg(v___x_3761_);
v___x_3769_ = l_Subarray_copy___redArg(v___x_3767_);
v___x_3770_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3763_);
lean_inc_ref(v___x_3768_);
lean_inc(v___x_3735_);
v___f_3771_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3771_, 0, v___x_3735_);
lean_closure_set(v___f_3771_, 1, v___x_3768_);
lean_closure_set(v___f_3771_, 2, v___x_3763_);
lean_closure_set(v___f_3771_, 3, v_all_3736_);
lean_closure_set(v___f_3771_, 4, v___x_3737_);
lean_closure_set(v___f_3771_, 5, v___x_3760_);
lean_closure_set(v___f_3771_, 6, v___x_3770_);
v___x_3772_ = lean_nat_sub(v___x_3756_, v___x_3770_);
lean_inc(v___x_3772_);
v___x_3773_ = l_Array_toSubarray___redArg(v_refArgs_3747_, v___x_3755_, v___x_3772_);
v___x_3774_ = l_Subarray_copy___redArg(v___x_3773_);
v___x_3775_ = lean_array_get(v___x_3738_, v_refArgs_3747_, v___x_3772_);
lean_dec(v___x_3772_);
lean_dec_ref(v_refArgs_3747_);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___x_3775_);
v___x_3776_ = lean_infer_type(v___x_3775_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
lean_inc(v___y_3752_);
lean_inc_ref(v___y_3751_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
v___x_3778_ = lean_infer_type(v_a_3777_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3780_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
v___x_3780_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3779_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
if (lean_obj_tag(v_a_3781_) == 1)
{
lean_object* v_val_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___f_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; size_t v_sz_3795_; size_t v___x_3796_; lean_object* v___x_3797_; 
v_val_3782_ = lean_ctor_get(v_a_3781_, 0);
lean_inc(v_val_3782_);
lean_dec_ref_known(v_a_3781_, 1);
v___x_3783_ = l_Lean_mkLevelMax(v_val_3782_, v_head_3739_);
v___x_3784_ = lean_array_get_size(v___x_3763_);
v___x_3785_ = l_Array_ofFn___redArg(v___x_3784_, v___f_3771_);
v___x_3786_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3787_ = lean_array_get_size(v___x_3785_);
lean_inc_ref(v___x_3785_);
v___x_3788_ = l_Array_toSubarray___redArg(v___x_3785_, v___x_3760_, v___x_3787_);
v___x_3789_ = lean_box(v___x_3757_);
lean_inc(v___x_3755_);
lean_inc_ref(v___x_3763_);
lean_inc_ref(v___x_3788_);
v___f_3790_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3790_, 0, v___x_3783_);
lean_closure_set(v___f_3790_, 1, v_tail_3740_);
lean_closure_set(v___f_3790_, 2, v_recName_3741_);
lean_closure_set(v___f_3790_, 3, v___x_3768_);
lean_closure_set(v___f_3790_, 4, v___x_3788_);
lean_closure_set(v___f_3790_, 5, v___x_3763_);
lean_closure_set(v___f_3790_, 6, v___x_3755_);
lean_closure_set(v___f_3790_, 7, v___x_3756_);
lean_closure_set(v___f_3790_, 8, v___x_3769_);
lean_closure_set(v___f_3790_, 9, v___x_3785_);
lean_closure_set(v___f_3790_, 10, v___x_3774_);
lean_closure_set(v___f_3790_, 11, v___x_3775_);
lean_closure_set(v___f_3790_, 12, v___x_3770_);
lean_closure_set(v___f_3790_, 13, v___x_3738_);
lean_closure_set(v___f_3790_, 14, v_val_3766_);
lean_closure_set(v___f_3790_, 15, v___x_3789_);
lean_closure_set(v___f_3790_, 16, v_brecOnGoName_3742_);
lean_closure_set(v___f_3790_, 17, v_levelParams_3743_);
lean_closure_set(v___f_3790_, 18, v___x_3735_);
lean_closure_set(v___f_3790_, 19, v_brecOnName_3744_);
lean_closure_set(v___f_3790_, 20, v___x_3760_);
lean_closure_set(v___f_3790_, 21, v_brecOnEqName_3745_);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v___x_3784_);
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3788_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3786_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v_sz_3795_ = lean_array_size(v___x_3763_);
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3755_, v___x_3756_, v___x_3763_, v_sz_3795_, v___x_3796_, v___x_3794_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3755_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_fst_3799_; uint8_t v___x_3800_; lean_object* v___x_3801_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v_fst_3799_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_fst_3799_);
lean_dec(v_a_3798_);
v___x_3800_ = 0;
v___x_3801_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3799_, v___f_3790_, v___x_3800_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3801_;
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v___f_3790_);
v_a_3802_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3797_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3797_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
else
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_dec(v_a_3781_);
lean_dec_ref(v___x_3774_);
lean_dec_ref(v___f_3771_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3755_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3735_);
v___x_3810_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3811_ = l_Lean_MessageData_ofExpr(v___x_3775_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3814_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3815_;
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec(v___x_3775_);
lean_dec_ref(v___x_3774_);
lean_dec_ref(v___f_3771_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3755_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3735_);
v_a_3816_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3780_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3780_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v___x_3775_);
lean_dec_ref(v___x_3774_);
lean_dec_ref(v___f_3771_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3755_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3735_);
v_a_3824_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3778_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3778_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v___x_3775_);
lean_dec_ref(v___x_3774_);
lean_dec_ref(v___f_3771_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v_val_3766_);
lean_dec_ref(v___x_3763_);
lean_dec(v___x_3755_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3735_);
v_a_3832_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3776_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3776_);
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
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec(v___x_3765_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3755_);
lean_dec(v___x_3754_);
lean_dec_ref(v_refArgs_3747_);
lean_dec(v_brecOnEqName_3745_);
lean_dec(v_brecOnName_3744_);
lean_dec(v_levelParams_3743_);
lean_dec(v_brecOnGoName_3742_);
lean_dec(v_recName_3741_);
lean_dec(v_tail_3740_);
lean_dec(v_head_3739_);
lean_dec_ref(v___x_3738_);
lean_dec(v___x_3737_);
lean_dec_ref(v_all_3736_);
lean_dec(v___x_3735_);
v___x_3840_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3841_ = l_Lean_MessageData_ofExpr(v_type_3746_);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = lean_array_to_list(v___x_3763_);
v___x_3846_ = lean_box(0);
v___x_3847_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3845_, v___x_3846_);
v___x_3848_ = l_Lean_MessageData_ofList(v___x_3847_);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3844_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3849_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3851_ = _args[0];
lean_object* v_numMotives_3852_ = _args[1];
lean_object* v_numMinors_3853_ = _args[2];
lean_object* v___x_3854_ = _args[3];
lean_object* v_all_3855_ = _args[4];
lean_object* v___x_3856_ = _args[5];
lean_object* v___x_3857_ = _args[6];
lean_object* v_head_3858_ = _args[7];
lean_object* v_tail_3859_ = _args[8];
lean_object* v_recName_3860_ = _args[9];
lean_object* v_brecOnGoName_3861_ = _args[10];
lean_object* v_levelParams_3862_ = _args[11];
lean_object* v_brecOnName_3863_ = _args[12];
lean_object* v_brecOnEqName_3864_ = _args[13];
lean_object* v_type_3865_ = _args[14];
lean_object* v_refArgs_3866_ = _args[15];
lean_object* v_refBody_3867_ = _args[16];
lean_object* v___y_3868_ = _args[17];
lean_object* v___y_3869_ = _args[18];
lean_object* v___y_3870_ = _args[19];
lean_object* v___y_3871_ = _args[20];
lean_object* v___y_3872_ = _args[21];
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3851_, v_numMotives_3852_, v_numMinors_3853_, v___x_3854_, v_all_3855_, v___x_3856_, v___x_3857_, v_head_3858_, v_tail_3859_, v_recName_3860_, v_brecOnGoName_3861_, v_levelParams_3862_, v_brecOnName_3863_, v_brecOnEqName_3864_, v_type_3865_, v_refArgs_3866_, v_refBody_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec_ref(v_refBody_3867_);
lean_dec(v_numMinors_3853_);
lean_dec(v_numMotives_3852_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3876_, lean_object* v_nParams_3877_, lean_object* v_all_3878_, lean_object* v_brecOnName_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v_brecOnGoName_3888_; lean_object* v___x_3889_; lean_object* v_brecOnEqName_3890_; lean_object* v___x_3891_; 
v___x_3885_ = l_Lean_instInhabitedExpr;
v___x_3886_ = lean_box(0);
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3879_, 2);
v_brecOnGoName_3888_ = l_Lean_Name_str___override(v_brecOnName_3879_, v___x_3887_);
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3890_ = l_Lean_Name_str___override(v_brecOnName_3879_, v___x_3889_);
lean_inc(v_recName_3876_);
v___x_3891_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3876_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3919_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3919_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3919_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
if (lean_obj_tag(v_a_3892_) == 7)
{
lean_object* v_val_3896_; lean_object* v_toConstantVal_3897_; lean_object* v_numMotives_3898_; lean_object* v_numMinors_3899_; lean_object* v_levelParams_3900_; lean_object* v_type_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
lean_del_object(v___x_3894_);
v_val_3896_ = lean_ctor_get(v_a_3892_, 0);
lean_inc_ref(v_val_3896_);
lean_dec_ref_known(v_a_3892_, 1);
v_toConstantVal_3897_ = lean_ctor_get(v_val_3896_, 0);
lean_inc_ref(v_toConstantVal_3897_);
v_numMotives_3898_ = lean_ctor_get(v_val_3896_, 4);
lean_inc(v_numMotives_3898_);
v_numMinors_3899_ = lean_ctor_get(v_val_3896_, 5);
lean_inc(v_numMinors_3899_);
lean_dec_ref(v_val_3896_);
v_levelParams_3900_ = lean_ctor_get(v_toConstantVal_3897_, 1);
lean_inc_n(v_levelParams_3900_, 2);
v_type_3901_ = lean_ctor_get(v_toConstantVal_3897_, 2);
lean_inc_ref(v_type_3901_);
lean_dec_ref(v_toConstantVal_3897_);
v___x_3902_ = lean_box(0);
v___x_3903_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3900_, v___x_3902_);
if (lean_obj_tag(v___x_3903_) == 1)
{
lean_object* v_head_3904_; lean_object* v_tail_3905_; lean_object* v___f_3906_; uint8_t v___x_3907_; lean_object* v___x_3908_; 
v_head_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_head_3904_);
v_tail_3905_ = lean_ctor_get(v___x_3903_, 1);
lean_inc(v_tail_3905_);
lean_inc_ref(v_type_3901_);
v___f_3906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3906_, 0, v_nParams_3877_);
lean_closure_set(v___f_3906_, 1, v_numMotives_3898_);
lean_closure_set(v___f_3906_, 2, v_numMinors_3899_);
lean_closure_set(v___f_3906_, 3, v___x_3903_);
lean_closure_set(v___f_3906_, 4, v_all_3878_);
lean_closure_set(v___f_3906_, 5, v___x_3886_);
lean_closure_set(v___f_3906_, 6, v___x_3885_);
lean_closure_set(v___f_3906_, 7, v_head_3904_);
lean_closure_set(v___f_3906_, 8, v_tail_3905_);
lean_closure_set(v___f_3906_, 9, v_recName_3876_);
lean_closure_set(v___f_3906_, 10, v_brecOnGoName_3888_);
lean_closure_set(v___f_3906_, 11, v_levelParams_3900_);
lean_closure_set(v___f_3906_, 12, v_brecOnName_3879_);
lean_closure_set(v___f_3906_, 13, v_brecOnEqName_3890_);
lean_closure_set(v___f_3906_, 14, v_type_3901_);
v___x_3907_ = 0;
v___x_3908_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3901_, v___f_3906_, v___x_3907_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
return v___x_3908_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_dec(v___x_3903_);
lean_dec_ref(v_type_3901_);
lean_dec(v_levelParams_3900_);
lean_dec(v_numMinors_3899_);
lean_dec(v_numMotives_3898_);
lean_dec(v_brecOnEqName_3890_);
lean_dec(v_brecOnGoName_3888_);
lean_dec(v_brecOnName_3879_);
lean_dec_ref(v_all_3878_);
lean_dec(v_nParams_3877_);
v___x_3909_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3910_ = l_Lean_MessageData_ofName(v_recName_3876_);
v___x_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
v___x_3914_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3913_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
return v___x_3914_;
}
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3917_; 
lean_dec(v_a_3892_);
lean_dec(v_brecOnEqName_3890_);
lean_dec(v_brecOnGoName_3888_);
lean_dec(v_brecOnName_3879_);
lean_dec_ref(v_all_3878_);
lean_dec(v_nParams_3877_);
lean_dec(v_recName_3876_);
v___x_3915_ = lean_box(0);
if (v_isShared_3895_ == 0)
{
lean_ctor_set(v___x_3894_, 0, v___x_3915_);
v___x_3917_ = v___x_3894_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v_brecOnEqName_3890_);
lean_dec(v_brecOnGoName_3888_);
lean_dec(v_brecOnName_3879_);
lean_dec_ref(v_all_3878_);
lean_dec(v_nParams_3877_);
lean_dec(v_recName_3876_);
v_a_3920_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3891_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3891_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3928_, lean_object* v_nParams_3929_, lean_object* v_all_3930_, lean_object* v_brecOnName_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3928_, v_nParams_3929_, v_all_3930_, v_brecOnName_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3938_, lean_object* v___x_3939_, lean_object* v___x_3940_, lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v_a_3943_, lean_object* v_b_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_nat_dec_lt(v_a_3943_, v_upperBound_3938_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec(v_a_3943_);
lean_dec_ref(v___x_3942_);
lean_dec(v___x_3941_);
lean_dec(v___x_3940_);
lean_dec(v___x_3939_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_b_3944_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3952_ = lean_box(0);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_nat_add(v_a_3943_, v___x_3953_);
lean_dec(v_a_3943_);
lean_inc_n(v___x_3954_, 2);
lean_inc(v___x_3939_);
v___x_3955_ = lean_name_append_index_after(v___x_3939_, v___x_3954_);
lean_inc(v___x_3940_);
v___x_3956_ = lean_name_append_index_after(v___x_3940_, v___x_3954_);
lean_inc_ref(v___x_3942_);
lean_inc(v___x_3941_);
v___x_3957_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3955_, v___x_3941_, v___x_3942_, v___x_3956_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_dec_ref_known(v___x_3957_, 1);
v_a_3943_ = v___x_3954_;
v_b_3944_ = v___x_3952_;
goto _start;
}
else
{
lean_dec(v___x_3954_);
lean_dec_ref(v___x_3942_);
lean_dec(v___x_3941_);
lean_dec(v___x_3940_);
lean_dec(v___x_3939_);
return v___x_3957_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v_a_3964_, lean_object* v_b_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3959_, v___x_3960_, v___x_3961_, v___x_3962_, v___x_3963_, v_a_3964_, v_b_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v_upperBound_3959_);
return v_res_3971_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3977_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3978_ = l_Lean_Name_append(v___x_3977_, v___x_3976_);
return v___x_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_toCold_3985_; lean_object* v_options_3986_; lean_object* v_inheritedTraceOptions_3987_; uint8_t v_hasTrace_3988_; lean_object* v___x_3989_; 
v_toCold_3985_ = lean_ctor_get(v_a_3982_, 0);
v_options_3986_ = lean_ctor_get(v_toCold_3985_, 2);
v_inheritedTraceOptions_3987_ = lean_ctor_get(v_toCold_3985_, 11);
v_hasTrace_3988_ = lean_ctor_get_uint8(v_options_3986_, sizeof(void*)*1);
v___x_3989_ = lean_box(0);
if (v_hasTrace_3988_ == 0)
{
lean_object* v___x_3990_; 
lean_inc(v_indName_3979_);
v___x_3990_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_4055_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_3993_ = v___x_3990_;
v_isShared_3994_ = v_isSharedCheck_4055_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3990_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_4055_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
if (lean_obj_tag(v_a_3991_) == 5)
{
lean_object* v_val_3995_; uint8_t v_isRec_3996_; 
v_val_3995_ = lean_ctor_get(v_a_3991_, 0);
lean_inc_ref(v_val_3995_);
lean_dec_ref_known(v_a_3991_, 1);
v_isRec_3996_ = lean_ctor_get_uint8(v_val_3995_, sizeof(void*)*6);
if (v_isRec_3996_ == 0)
{
lean_object* v___x_3997_; lean_object* v___x_3999_; 
lean_dec_ref(v_val_3995_);
lean_dec(v_indName_3979_);
v___x_3997_ = lean_box(0);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_3997_);
v___x_3999_ = v___x_3993_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
else
{
lean_object* v_toConstantVal_4001_; lean_object* v_numParams_4002_; lean_object* v_all_4003_; lean_object* v_numNested_4004_; lean_object* v_type_4005_; lean_object* v___x_4006_; 
lean_del_object(v___x_3993_);
v_toConstantVal_4001_ = lean_ctor_get(v_val_3995_, 0);
lean_inc_ref(v_toConstantVal_4001_);
v_numParams_4002_ = lean_ctor_get(v_val_3995_, 1);
lean_inc(v_numParams_4002_);
v_all_4003_ = lean_ctor_get(v_val_3995_, 3);
lean_inc(v_all_4003_);
v_numNested_4004_ = lean_ctor_get(v_val_3995_, 5);
lean_inc(v_numNested_4004_);
lean_dec_ref(v_val_3995_);
v_type_4005_ = lean_ctor_get(v_toConstantVal_4001_, 2);
lean_inc_ref(v_type_4005_);
lean_dec_ref(v_toConstantVal_4001_);
v___x_4006_ = l_Lean_Meta_isPropFormerType(v_type_4005_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4042_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4009_ = v___x_4006_;
v_isShared_4010_ = v_isSharedCheck_4042_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_4006_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4042_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
uint8_t v___x_4011_; 
v___x_4011_ = lean_unbox(v_a_4007_);
lean_dec(v_a_4007_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_del_object(v___x_4009_);
lean_inc_n(v_indName_3979_, 2);
v___x_4012_ = l_Lean_mkRecName(v_indName_3979_);
v___x_4013_ = l_Lean_mkBRecOnName(v_indName_3979_);
lean_inc(v_all_4003_);
v___x_4014_ = lean_array_mk(v_all_4003_);
lean_inc(v___x_4013_);
lean_inc_ref(v___x_4014_);
lean_inc(v_numParams_4002_);
lean_inc(v___x_4012_);
v___x_4015_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4012_, v_numParams_4002_, v___x_4014_, v___x_4013_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4036_; 
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4036_ == 0)
{
lean_object* v_unused_4037_; 
v_unused_4037_ = lean_ctor_get(v___x_4015_, 0);
lean_dec(v_unused_4037_);
v___x_4017_ = v___x_4015_;
v_isShared_4018_ = v_isSharedCheck_4036_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v___x_4015_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4036_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; uint8_t v___x_4021_; 
v___x_4019_ = lean_unsigned_to_nat(0u);
v___x_4020_ = l_List_get_x21Internal___redArg(v___x_3989_, v_all_4003_, v___x_4019_);
lean_dec(v_all_4003_);
v___x_4021_ = lean_name_eq(v___x_4020_, v_indName_3979_);
lean_dec(v_indName_3979_);
lean_dec(v___x_4020_);
if (v___x_4021_ == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
lean_dec_ref(v___x_4014_);
lean_dec(v___x_4013_);
lean_dec(v___x_4012_);
lean_dec(v_numNested_4004_);
lean_dec(v_numParams_4002_);
v___x_4022_ = lean_box(0);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4022_);
v___x_4024_ = v___x_4017_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
else
{
lean_object* v___x_4026_; lean_object* v___x_4027_; 
lean_del_object(v___x_4017_);
v___x_4026_ = lean_box(0);
v___x_4027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4004_, v___x_4012_, v___x_4013_, v_numParams_4002_, v___x_4014_, v___x_4019_, v___x_4026_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_numNested_4004_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v___x_4027_, 0);
lean_dec(v_unused_4035_);
v___x_4029_ = v___x_4027_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_dec(v___x_4027_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
lean_ctor_set(v___x_4029_, 0, v___x_4026_);
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4026_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
else
{
return v___x_4027_;
}
}
}
}
else
{
lean_dec_ref(v___x_4014_);
lean_dec(v___x_4013_);
lean_dec(v___x_4012_);
lean_dec(v_numNested_4004_);
lean_dec(v_all_4003_);
lean_dec(v_numParams_4002_);
lean_dec(v_indName_3979_);
return v___x_4015_;
}
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_dec(v_numNested_4004_);
lean_dec(v_all_4003_);
lean_dec(v_numParams_4002_);
lean_dec(v_indName_3979_);
v___x_4038_ = lean_box(0);
if (v_isShared_4010_ == 0)
{
lean_ctor_set(v___x_4009_, 0, v___x_4038_);
v___x_4040_ = v___x_4009_;
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
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_numNested_4004_);
lean_dec(v_all_4003_);
lean_dec(v_numParams_4002_);
lean_dec(v_indName_3979_);
v_a_4043_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4006_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4006_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4053_; 
lean_dec(v_a_3991_);
lean_dec(v_indName_3979_);
v___x_4051_ = lean_box(0);
if (v_isShared_3994_ == 0)
{
lean_ctor_set(v___x_3993_, 0, v___x_4051_);
v___x_4053_ = v___x_3993_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_indName_3979_);
v_a_4056_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_3990_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_3990_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_object* v___f_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v_a_4072_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v_a_4087_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v_a_4092_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v_a_4097_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v_a_4109_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v_a_4114_; 
lean_inc(v_indName_3979_);
v___f_4064_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4064_, 0, v_indName_3979_);
v___x_4065_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4066_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4067_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3987_, v_options_3986_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4181_ = l_Lean_trace_profiler;
v___x_4182_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3986_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; 
lean_dec_ref(v___f_4064_);
lean_inc(v_indName_3979_);
v___x_4183_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4248_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4186_ = v___x_4183_;
v_isShared_4187_ = v_isSharedCheck_4248_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4183_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4248_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
if (lean_obj_tag(v_a_4184_) == 5)
{
lean_object* v_val_4188_; uint8_t v_isRec_4189_; 
v_val_4188_ = lean_ctor_get(v_a_4184_, 0);
lean_inc_ref(v_val_4188_);
lean_dec_ref_known(v_a_4184_, 1);
v_isRec_4189_ = lean_ctor_get_uint8(v_val_4188_, sizeof(void*)*6);
if (v_isRec_4189_ == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
lean_dec_ref(v_val_4188_);
lean_dec(v_indName_3979_);
v___x_4190_ = lean_box(0);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4190_);
v___x_4192_ = v___x_4186_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4190_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
else
{
lean_object* v_toConstantVal_4194_; lean_object* v_numParams_4195_; lean_object* v_all_4196_; lean_object* v_numNested_4197_; lean_object* v_type_4198_; lean_object* v___x_4199_; 
lean_del_object(v___x_4186_);
v_toConstantVal_4194_ = lean_ctor_get(v_val_4188_, 0);
lean_inc_ref(v_toConstantVal_4194_);
v_numParams_4195_ = lean_ctor_get(v_val_4188_, 1);
lean_inc(v_numParams_4195_);
v_all_4196_ = lean_ctor_get(v_val_4188_, 3);
lean_inc(v_all_4196_);
v_numNested_4197_ = lean_ctor_get(v_val_4188_, 5);
lean_inc(v_numNested_4197_);
lean_dec_ref(v_val_4188_);
v_type_4198_ = lean_ctor_get(v_toConstantVal_4194_, 2);
lean_inc_ref(v_type_4198_);
lean_dec_ref(v_toConstantVal_4194_);
v___x_4199_ = l_Lean_Meta_isPropFormerType(v_type_4198_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4235_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4202_ = v___x_4199_;
v_isShared_4203_ = v_isSharedCheck_4235_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4199_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4235_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
uint8_t v___x_4204_; 
v___x_4204_ = lean_unbox(v_a_4200_);
lean_dec(v_a_4200_);
if (v___x_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
lean_del_object(v___x_4202_);
lean_inc_n(v_indName_3979_, 2);
v___x_4205_ = l_Lean_mkRecName(v_indName_3979_);
v___x_4206_ = l_Lean_mkBRecOnName(v_indName_3979_);
lean_inc(v_all_4196_);
v___x_4207_ = lean_array_mk(v_all_4196_);
lean_inc(v___x_4206_);
lean_inc_ref(v___x_4207_);
lean_inc(v_numParams_4195_);
lean_inc(v___x_4205_);
v___x_4208_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4205_, v_numParams_4195_, v___x_4207_, v___x_4206_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4229_; 
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4229_ == 0)
{
lean_object* v_unused_4230_; 
v_unused_4230_ = lean_ctor_get(v___x_4208_, 0);
lean_dec(v_unused_4230_);
v___x_4210_ = v___x_4208_;
v_isShared_4211_ = v_isSharedCheck_4229_;
goto v_resetjp_4209_;
}
else
{
lean_dec(v___x_4208_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4229_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = l_List_get_x21Internal___redArg(v___x_3989_, v_all_4196_, v___x_4212_);
lean_dec(v_all_4196_);
v___x_4214_ = lean_name_eq(v___x_4213_, v_indName_3979_);
lean_dec(v_indName_3979_);
lean_dec(v___x_4213_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; lean_object* v___x_4217_; 
lean_dec_ref(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec(v___x_4205_);
lean_dec(v_numNested_4197_);
lean_dec(v_numParams_4195_);
v___x_4215_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4215_);
v___x_4217_ = v___x_4210_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
else
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_del_object(v___x_4210_);
v___x_4219_ = lean_box(0);
v___x_4220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4197_, v___x_4205_, v___x_4206_, v_numParams_4195_, v___x_4207_, v___x_4212_, v___x_4219_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_numNested_4197_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; 
v_unused_4228_ = lean_ctor_get(v___x_4220_, 0);
lean_dec(v_unused_4228_);
v___x_4222_ = v___x_4220_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_dec(v___x_4220_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4219_);
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4219_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
else
{
return v___x_4220_;
}
}
}
}
else
{
lean_dec_ref(v___x_4207_);
lean_dec(v___x_4206_);
lean_dec(v___x_4205_);
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_3979_);
return v___x_4208_;
}
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4233_; 
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_3979_);
v___x_4231_ = lean_box(0);
if (v_isShared_4203_ == 0)
{
lean_ctor_set(v___x_4202_, 0, v___x_4231_);
v___x_4233_ = v___x_4202_;
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
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_numNested_4197_);
lean_dec(v_all_4196_);
lean_dec(v_numParams_4195_);
lean_dec(v_indName_3979_);
v_a_4236_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4199_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4199_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
}
else
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_dec(v_a_4184_);
lean_dec(v_indName_3979_);
v___x_4244_ = lean_box(0);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4244_);
v___x_4246_ = v___x_4186_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4244_);
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
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec(v_indName_3979_);
v_a_4249_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4183_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4183_);
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
}
else
{
goto v___jp_4116_;
}
}
else
{
goto v___jp_4116_;
}
v___jp_4069_:
{
lean_object* v___x_4073_; double v___x_4074_; double v___x_4075_; double v___x_4076_; double v___x_4077_; double v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4073_ = lean_io_mono_nanos_now();
v___x_4074_ = lean_float_of_nat(v___y_4070_);
v___x_4075_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4076_ = lean_float_div(v___x_4074_, v___x_4075_);
v___x_4077_ = lean_float_of_nat(v___x_4073_);
v___x_4078_ = lean_float_div(v___x_4077_, v___x_4075_);
v___x_4079_ = lean_box_float(v___x_4076_);
v___x_4080_ = lean_box_float(v___x_4078_);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4072_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4065_, v_hasTrace_3988_, v___x_4066_, v_options_3986_, v___x_4068_, v___y_4071_, v___f_4064_, v___x_4082_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4083_;
}
v___jp_4084_:
{
lean_object* v___x_4088_; 
v___x_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4088_, 0, v_a_4087_);
v___y_4070_ = v___y_4085_;
v___y_4071_ = v___y_4086_;
v_a_4072_ = v___x_4088_;
goto v___jp_4069_;
}
v___jp_4089_:
{
lean_object* v___x_4093_; 
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4092_);
v___y_4070_ = v___y_4090_;
v___y_4071_ = v___y_4091_;
v_a_4072_ = v___x_4093_;
goto v___jp_4069_;
}
v___jp_4094_:
{
lean_object* v___x_4098_; double v___x_4099_; double v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4098_ = lean_io_get_num_heartbeats();
v___x_4099_ = lean_float_of_nat(v___y_4096_);
v___x_4100_ = lean_float_of_nat(v___x_4098_);
v___x_4101_ = lean_box_float(v___x_4099_);
v___x_4102_ = lean_box_float(v___x_4100_);
v___x_4103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4101_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v_a_4097_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4065_, v_hasTrace_3988_, v___x_4066_, v_options_3986_, v___x_4068_, v___y_4095_, v___f_4064_, v___x_4104_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_4105_;
}
v___jp_4106_:
{
lean_object* v___x_4110_; 
v___x_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4110_, 0, v_a_4109_);
v___y_4095_ = v___y_4107_;
v___y_4096_ = v___y_4108_;
v_a_4097_ = v___x_4110_;
goto v___jp_4094_;
}
v___jp_4111_:
{
lean_object* v___x_4115_; 
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_a_4114_);
v___y_4095_ = v___y_4112_;
v___y_4096_ = v___y_4113_;
v_a_4097_ = v___x_4115_;
goto v___jp_4094_;
}
v___jp_4116_:
{
lean_object* v___x_4117_; lean_object* v_a_4118_; lean_object* v___x_4119_; uint8_t v___x_4120_; 
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3983_);
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref(v___x_4117_);
v___x_4119_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4120_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3986_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3979_);
v___x_4122_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
if (lean_obj_tag(v_a_4123_) == 5)
{
lean_object* v_val_4124_; uint8_t v_isRec_4125_; 
v_val_4124_ = lean_ctor_get(v_a_4123_, 0);
lean_inc_ref(v_val_4124_);
lean_dec_ref_known(v_a_4123_, 1);
v_isRec_4125_ = lean_ctor_get_uint8(v_val_4124_, sizeof(void*)*6);
if (v_isRec_4125_ == 0)
{
lean_object* v___x_4126_; 
lean_dec_ref(v_val_4124_);
lean_dec(v_indName_3979_);
v___x_4126_ = lean_box(0);
v___y_4085_ = v___x_4121_;
v___y_4086_ = v_a_4118_;
v_a_4087_ = v___x_4126_;
goto v___jp_4084_;
}
else
{
lean_object* v_toConstantVal_4127_; lean_object* v_numParams_4128_; lean_object* v_all_4129_; lean_object* v_numNested_4130_; lean_object* v_type_4131_; lean_object* v___x_4132_; 
v_toConstantVal_4127_ = lean_ctor_get(v_val_4124_, 0);
lean_inc_ref(v_toConstantVal_4127_);
v_numParams_4128_ = lean_ctor_get(v_val_4124_, 1);
lean_inc(v_numParams_4128_);
v_all_4129_ = lean_ctor_get(v_val_4124_, 3);
lean_inc(v_all_4129_);
v_numNested_4130_ = lean_ctor_get(v_val_4124_, 5);
lean_inc(v_numNested_4130_);
lean_dec_ref(v_val_4124_);
v_type_4131_ = lean_ctor_get(v_toConstantVal_4127_, 2);
lean_inc_ref(v_type_4131_);
lean_dec_ref(v_toConstantVal_4127_);
v___x_4132_ = l_Lean_Meta_isPropFormerType(v_type_4131_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; uint8_t v___x_4134_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = lean_unbox(v_a_4133_);
lean_dec(v_a_4133_);
if (v___x_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_inc_n(v_indName_3979_, 2);
v___x_4135_ = l_Lean_mkRecName(v_indName_3979_);
v___x_4136_ = l_Lean_mkBRecOnName(v_indName_3979_);
lean_inc(v_all_4129_);
v___x_4137_ = lean_array_mk(v_all_4129_);
lean_inc(v___x_4136_);
lean_inc_ref(v___x_4137_);
lean_inc(v_numParams_4128_);
lean_inc(v___x_4135_);
v___x_4138_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4135_, v_numParams_4128_, v___x_4137_, v___x_4136_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
lean_dec_ref_known(v___x_4138_, 1);
v___x_4139_ = lean_unsigned_to_nat(0u);
v___x_4140_ = l_List_get_x21Internal___redArg(v___x_3989_, v_all_4129_, v___x_4139_);
lean_dec(v_all_4129_);
v___x_4141_ = lean_name_eq(v___x_4140_, v_indName_3979_);
lean_dec(v_indName_3979_);
lean_dec(v___x_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; 
lean_dec_ref(v___x_4137_);
lean_dec(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v_numNested_4130_);
lean_dec(v_numParams_4128_);
v___x_4142_ = lean_box(0);
v___y_4085_ = v___x_4121_;
v___y_4086_ = v_a_4118_;
v_a_4087_ = v___x_4142_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = lean_box(0);
v___x_4144_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4130_, v___x_4135_, v___x_4136_, v_numParams_4128_, v___x_4137_, v___x_4139_, v___x_4143_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_numNested_4130_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_dec_ref_known(v___x_4144_, 1);
v___y_4085_ = v___x_4121_;
v___y_4086_ = v_a_4118_;
v_a_4087_ = v___x_4143_;
goto v___jp_4084_;
}
else
{
lean_object* v_a_4145_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
v___y_4090_ = v___x_4121_;
v___y_4091_ = v_a_4118_;
v_a_4092_ = v_a_4145_;
goto v___jp_4089_;
}
}
}
else
{
lean_object* v_a_4146_; 
lean_dec_ref(v___x_4137_);
lean_dec(v___x_4136_);
lean_dec(v___x_4135_);
lean_dec(v_numNested_4130_);
lean_dec(v_all_4129_);
lean_dec(v_numParams_4128_);
lean_dec(v_indName_3979_);
v_a_4146_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4138_, 1);
v___y_4090_ = v___x_4121_;
v___y_4091_ = v_a_4118_;
v_a_4092_ = v_a_4146_;
goto v___jp_4089_;
}
}
else
{
lean_object* v___x_4147_; 
lean_dec(v_numNested_4130_);
lean_dec(v_all_4129_);
lean_dec(v_numParams_4128_);
lean_dec(v_indName_3979_);
v___x_4147_ = lean_box(0);
v___y_4085_ = v___x_4121_;
v___y_4086_ = v_a_4118_;
v_a_4087_ = v___x_4147_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4148_; 
lean_dec(v_numNested_4130_);
lean_dec(v_all_4129_);
lean_dec(v_numParams_4128_);
lean_dec(v_indName_3979_);
v_a_4148_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4132_, 1);
v___y_4090_ = v___x_4121_;
v___y_4091_ = v_a_4118_;
v_a_4092_ = v_a_4148_;
goto v___jp_4089_;
}
}
}
else
{
lean_object* v___x_4149_; 
lean_dec(v_a_4123_);
lean_dec(v_indName_3979_);
v___x_4149_ = lean_box(0);
v___y_4085_ = v___x_4121_;
v___y_4086_ = v_a_4118_;
v_a_4087_ = v___x_4149_;
goto v___jp_4084_;
}
}
else
{
lean_object* v_a_4150_; 
lean_dec(v_indName_3979_);
v_a_4150_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4122_, 1);
v___y_4090_ = v___x_4121_;
v___y_4091_ = v_a_4118_;
v_a_4092_ = v_a_4150_;
goto v___jp_4089_;
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3979_);
v___x_4152_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
if (lean_obj_tag(v_a_4153_) == 5)
{
lean_object* v_val_4154_; uint8_t v_isRec_4155_; 
v_val_4154_ = lean_ctor_get(v_a_4153_, 0);
lean_inc_ref(v_val_4154_);
lean_dec_ref_known(v_a_4153_, 1);
v_isRec_4155_ = lean_ctor_get_uint8(v_val_4154_, sizeof(void*)*6);
if (v_isRec_4155_ == 0)
{
lean_object* v___x_4156_; 
lean_dec_ref(v_val_4154_);
lean_dec(v_indName_3979_);
v___x_4156_ = lean_box(0);
v___y_4107_ = v_a_4118_;
v___y_4108_ = v___x_4151_;
v_a_4109_ = v___x_4156_;
goto v___jp_4106_;
}
else
{
lean_object* v_toConstantVal_4157_; lean_object* v_numParams_4158_; lean_object* v_all_4159_; lean_object* v_numNested_4160_; lean_object* v_type_4161_; lean_object* v___x_4162_; 
v_toConstantVal_4157_ = lean_ctor_get(v_val_4154_, 0);
lean_inc_ref(v_toConstantVal_4157_);
v_numParams_4158_ = lean_ctor_get(v_val_4154_, 1);
lean_inc(v_numParams_4158_);
v_all_4159_ = lean_ctor_get(v_val_4154_, 3);
lean_inc(v_all_4159_);
v_numNested_4160_ = lean_ctor_get(v_val_4154_, 5);
lean_inc(v_numNested_4160_);
lean_dec_ref(v_val_4154_);
v_type_4161_ = lean_ctor_get(v_toConstantVal_4157_, 2);
lean_inc_ref(v_type_4161_);
lean_dec_ref(v_toConstantVal_4157_);
v___x_4162_ = l_Lean_Meta_isPropFormerType(v_type_4161_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; uint8_t v___x_4164_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = lean_unbox(v_a_4163_);
lean_dec(v_a_4163_);
if (v___x_4164_ == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
lean_inc_n(v_indName_3979_, 2);
v___x_4165_ = l_Lean_mkRecName(v_indName_3979_);
v___x_4166_ = l_Lean_mkBRecOnName(v_indName_3979_);
lean_inc(v_all_4159_);
v___x_4167_ = lean_array_mk(v_all_4159_);
lean_inc(v___x_4166_);
lean_inc_ref(v___x_4167_);
lean_inc(v_numParams_4158_);
lean_inc(v___x_4165_);
v___x_4168_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4165_, v_numParams_4158_, v___x_4167_, v___x_4166_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
lean_dec_ref_known(v___x_4168_, 1);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = l_List_get_x21Internal___redArg(v___x_3989_, v_all_4159_, v___x_4169_);
lean_dec(v_all_4159_);
v___x_4171_ = lean_name_eq(v___x_4170_, v_indName_3979_);
lean_dec(v_indName_3979_);
lean_dec(v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v___x_4167_);
lean_dec(v___x_4166_);
lean_dec(v___x_4165_);
lean_dec(v_numNested_4160_);
lean_dec(v_numParams_4158_);
v___x_4172_ = lean_box(0);
v___y_4107_ = v_a_4118_;
v___y_4108_ = v___x_4151_;
v_a_4109_ = v___x_4172_;
goto v___jp_4106_;
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_box(0);
v___x_4174_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4160_, v___x_4165_, v___x_4166_, v_numParams_4158_, v___x_4167_, v___x_4169_, v___x_4173_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_numNested_4160_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_dec_ref_known(v___x_4174_, 1);
v___y_4107_ = v_a_4118_;
v___y_4108_ = v___x_4151_;
v_a_4109_ = v___x_4173_;
goto v___jp_4106_;
}
else
{
lean_object* v_a_4175_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___y_4112_ = v_a_4118_;
v___y_4113_ = v___x_4151_;
v_a_4114_ = v_a_4175_;
goto v___jp_4111_;
}
}
}
else
{
lean_object* v_a_4176_; 
lean_dec_ref(v___x_4167_);
lean_dec(v___x_4166_);
lean_dec(v___x_4165_);
lean_dec(v_numNested_4160_);
lean_dec(v_all_4159_);
lean_dec(v_numParams_4158_);
lean_dec(v_indName_3979_);
v_a_4176_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_4112_ = v_a_4118_;
v___y_4113_ = v___x_4151_;
v_a_4114_ = v_a_4176_;
goto v___jp_4111_;
}
}
else
{
lean_object* v___x_4177_; 
lean_dec(v_numNested_4160_);
lean_dec(v_all_4159_);
lean_dec(v_numParams_4158_);
lean_dec(v_indName_3979_);
v___x_4177_ = lean_box(0);
v___y_4107_ = v_a_4118_;
v___y_4108_ = v___x_4151_;
v_a_4109_ = v___x_4177_;
goto v___jp_4106_;
}
}
else
{
lean_object* v_a_4178_; 
lean_dec(v_numNested_4160_);
lean_dec(v_all_4159_);
lean_dec(v_numParams_4158_);
lean_dec(v_indName_3979_);
v_a_4178_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4162_, 1);
v___y_4112_ = v_a_4118_;
v___y_4113_ = v___x_4151_;
v_a_4114_ = v_a_4178_;
goto v___jp_4111_;
}
}
}
else
{
lean_object* v___x_4179_; 
lean_dec(v_a_4153_);
lean_dec(v_indName_3979_);
v___x_4179_ = lean_box(0);
v___y_4107_ = v_a_4118_;
v___y_4108_ = v___x_4151_;
v_a_4109_ = v___x_4179_;
goto v___jp_4106_;
}
}
else
{
lean_object* v_a_4180_; 
lean_dec(v_indName_3979_);
v_a_4180_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4152_, 1);
v___y_4112_ = v_a_4118_;
v___y_4113_ = v___x_4151_;
v_a_4114_ = v_a_4180_;
goto v___jp_4111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_){
_start:
{
lean_object* v_res_4263_; 
v_res_4263_ = l_Lean_mkBRecOn(v_indName_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_);
lean_dec(v_a_4261_);
lean_dec_ref(v_a_4260_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v___x_4267_, lean_object* v___x_4268_, lean_object* v_inst_4269_, lean_object* v_R_4270_, lean_object* v_a_4271_, lean_object* v_b_4272_, lean_object* v_c_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_){
_start:
{
lean_object* v___x_4279_; 
v___x_4279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4264_, v___x_4265_, v___x_4266_, v___x_4267_, v___x_4268_, v_a_4271_, v_b_4272_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
return v___x_4279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v_inst_4285_, lean_object* v_R_4286_, lean_object* v_a_4287_, lean_object* v_b_4288_, lean_object* v_c_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4280_, v___x_4281_, v___x_4282_, v___x_4283_, v___x_4284_, v_inst_4285_, v_R_4286_, v_a_4287_, v_b_4288_, v_c_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v_upperBound_4280_);
return v_res_4295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_unsigned_to_nat(2304625798u);
v___x_4342_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4343_ = l_Lean_Name_num___override(v___x_4342_, v___x_4341_);
return v___x_4343_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4345_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4346_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4347_ = l_Lean_Name_str___override(v___x_4346_, v___x_4345_);
return v___x_4347_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4350_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4351_ = l_Lean_Name_str___override(v___x_4350_, v___x_4349_);
return v___x_4351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_unsigned_to_nat(2u);
v___x_4353_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4354_ = l_Lean_Name_num___override(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4356_; uint8_t v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4356_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4357_ = 0;
v___x_4358_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4359_ = l_Lean_registerTraceClass(v___x_4356_, v___x_4357_, v___x_4358_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4361_;
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
