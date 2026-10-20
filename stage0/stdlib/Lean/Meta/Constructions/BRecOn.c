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
uint8_t v___x_9025__boxed_554_; lean_object* v_res_555_; 
v___x_9025__boxed_554_ = lean_unbox(v___x_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_545_, v___x_9025__boxed_554_, v_targs_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
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
v___x_830_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_ctor_set(v___x_830_, 2, v___x_829_);
lean_ctor_set(v___x_830_, 3, v___x_829_);
lean_ctor_set(v___x_830_, 4, v___x_829_);
lean_ctor_set(v___x_830_, 5, v___x_829_);
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
lean_object* v_toCold_905_; lean_object* v_currRecDepth_906_; lean_object* v_ref_907_; uint16_t v_optionFlags_908_; uint8_t v_suppressElabErrors_909_; uint8_t v_isRecordingDeps_910_; lean_object* v_ref_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_toCold_905_ = lean_ctor_get(v___y_902_, 0);
v_currRecDepth_906_ = lean_ctor_get(v___y_902_, 1);
v_ref_907_ = lean_ctor_get(v___y_902_, 2);
v_optionFlags_908_ = lean_ctor_get_uint16(v___y_902_, sizeof(void*)*3);
v_suppressElabErrors_909_ = lean_ctor_get_uint8(v___y_902_, sizeof(void*)*3 + 2);
v_isRecordingDeps_910_ = lean_ctor_get_uint8(v___y_902_, sizeof(void*)*3 + 3);
v_ref_911_ = l_Lean_replaceRef(v_ref_898_, v_ref_907_);
lean_inc(v_currRecDepth_906_);
lean_inc_ref(v_toCold_905_);
v___x_912_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_912_, 0, v_toCold_905_);
lean_ctor_set(v___x_912_, 1, v_currRecDepth_906_);
lean_ctor_set(v___x_912_, 2, v_ref_911_);
lean_ctor_set_uint16(v___x_912_, sizeof(void*)*3, v_optionFlags_908_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*3 + 2, v_suppressElabErrors_909_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*3 + 3, v_isRecordingDeps_910_);
v___x_913_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_899_, v___y_900_, v___y_901_, v___x_912_, v___y_903_);
lean_dec_ref_known(v___x_912_, 3);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_914_, lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_914_, v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v_ref_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_925_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
lean_ctor_set(v___x_927_, 2, v___x_926_);
lean_ctor_set(v___x_927_, 3, v___x_926_);
lean_ctor_set(v___x_927_, 4, v___x_925_);
lean_ctor_set(v___x_927_, 5, v___x_925_);
lean_ctor_set(v___x_927_, 6, v___x_925_);
lean_ctor_set(v___x_927_, 7, v___x_925_);
lean_ctor_set(v___x_927_, 8, v___x_925_);
lean_ctor_set(v___x_927_, 9, v___x_925_);
lean_ctor_set(v___x_927_, 10, v___x_925_);
lean_ctor_set(v___x_927_, 11, v___x_924_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(32u);
v___x_929_ = lean_mk_empty_array_with_capacity(v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_931_ = ((size_t)5ULL);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_unsigned_to_nat(32u);
v___x_934_ = lean_mk_empty_array_with_capacity(v___x_933_);
v___x_935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
lean_ctor_set(v___x_936_, 2, v___x_932_);
lean_ctor_set(v___x_936_, 3, v___x_932_);
lean_ctor_set_usize(v___x_936_, 4, v___x_931_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_937_ = lean_box(1);
v___x_938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_940_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_938_);
lean_ctor_set(v___x_940_, 2, v___x_937_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_962_, lean_object* v_declHint_963_, lean_object* v___y_964_){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_env_968_; uint8_t v___x_969_; 
v___x_966_ = lean_box(0);
v___x_967_ = lean_st_ref_get(v___y_964_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_969_ = l_Lean_Name_isAnonymous(v_declHint_963_);
if (v___x_969_ == 0)
{
uint8_t v_isExporting_970_; 
v_isExporting_970_ = lean_ctor_get_uint8(v_env_968_, sizeof(void*)*13);
if (v_isExporting_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_963_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_msg_962_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
lean_inc_ref(v_env_968_);
v___x_972_ = l_Lean_Environment_setExporting(v_env_968_, v___x_969_);
lean_inc(v_declHint_963_);
lean_inc_ref(v___x_972_);
v___x_973_ = l_Lean_Environment_contains(v___x_972_, v_declHint_963_, v_isExporting_970_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_963_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_msg_962_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_c_980_; lean_object* v___x_981_; 
v___x_975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_977_ = l_Lean_Options_empty;
v___x_978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_978_, 0, v___x_972_);
lean_ctor_set(v___x_978_, 1, v___x_975_);
lean_ctor_set(v___x_978_, 2, v___x_976_);
lean_ctor_set(v___x_978_, 3, v___x_977_);
lean_inc(v_declHint_963_);
v___x_979_ = l_Lean_MessageData_ofConstName(v_declHint_963_, v___x_969_);
v_c_980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_980_, 0, v___x_978_);
lean_ctor_set(v_c_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_968_, v_declHint_963_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_963_);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_c_980_);
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Lean_MessageData_note(v___x_985_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v_msg_962_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1023_; 
v_val_989_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_991_ = v___x_981_;
v_isShared_992_ = v_isSharedCheck_1023_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_val_989_);
lean_dec(v___x_981_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1023_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_moduleNames_994_; lean_object* v_mod_995_; uint8_t v___x_996_; 
v___x_993_ = l_Lean_Environment_header(v_env_968_);
lean_dec_ref(v_env_968_);
v_moduleNames_994_ = lean_ctor_get(v___x_993_, 4);
lean_inc_ref(v_moduleNames_994_);
lean_dec_ref(v___x_993_);
v_mod_995_ = lean_array_get(v___x_966_, v_moduleNames_994_, v_val_989_);
lean_dec(v_val_989_);
lean_dec_ref(v_moduleNames_994_);
v___x_996_ = l_Lean_isPrivateName(v_declHint_963_);
lean_dec(v_declHint_963_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_c_980_);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_MessageData_ofName(v_mod_995_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_MessageData_note(v___x_1004_);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_msg_962_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 0);
lean_ctor_set(v___x_991_, 0, v___x_1006_);
v___x_1008_ = v___x_991_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v_c_980_);
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_MessageData_ofName(v_mod_995_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_MessageData_note(v___x_1017_);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v_msg_962_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 0);
lean_ctor_set(v___x_991_, 0, v___x_1019_);
v___x_1021_ = v___x_991_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1024_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_963_);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v_msg_962_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1025_, lean_object* v_declHint_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1025_, v_declHint_1026_, v___y_1027_);
lean_dec(v___y_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1030_, lean_object* v_declHint_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1047_; 
v___x_1037_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1030_, v_declHint_1031_, v___y_1035_);
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1047_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1042_ = l_Lean_unknownIdentifierMessageTag;
v___x_1043_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1048_, lean_object* v_declHint_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1048_, v_declHint_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1056_, lean_object* v_msg_1057_, lean_object* v_declHint_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v_a_1065_; lean_object* v___x_1066_; 
v___x_1064_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1057_, v_declHint_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1056_, v_a_1065_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1067_, lean_object* v_msg_1068_, lean_object* v_declHint_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1067_, v_msg_1068_, v_declHint_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v_ref_1067_);
return v_res_1075_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1082_, lean_object* v_constName_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1089_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1090_ = 0;
lean_inc(v_constName_1083_);
v___x_1091_ = l_Lean_MessageData_ofConstName(v_constName_1083_, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1089_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1082_, v___x_1094_, v_constName_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1096_, lean_object* v_constName_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1096_, v_constName_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v_ref_1096_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_ref_1110_; lean_object* v___x_1111_; 
v_ref_1110_ = lean_ctor_get(v___y_1107_, 2);
v___x_1111_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1110_, v_constName_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v_env_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = lean_st_ref_get(v___y_1123_);
v_env_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc_ref(v_env_1126_);
lean_dec(v___x_1125_);
v___x_1127_ = 0;
lean_inc(v_constName_1119_);
v___x_1128_ = l_Lean_Environment_find_x3f(v_env_1126_, v_constName_1119_, v___x_1127_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1129_;
}
else
{
lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec(v_constName_1119_);
v_val_1130_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1128_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v___x_1128_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set_tag(v___x_1132_, 0);
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_val_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1154_, lean_object* v_nParams_1155_, lean_object* v_belowName_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1154_);
v___x_1163_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1154_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
if (lean_obj_tag(v_a_1164_) == 7)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1282_; 
v_val_1165_ = lean_ctor_get(v_a_1164_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1167_ = v_a_1164_;
v_isShared_1168_ = v_isSharedCheck_1282_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v_a_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1282_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_toConstantVal_1169_; lean_object* v_numMotives_1170_; lean_object* v_numMinors_1171_; lean_object* v_levelParams_1172_; lean_object* v_type_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v_toConstantVal_1169_ = lean_ctor_get(v_val_1165_, 0);
lean_inc_ref(v_toConstantVal_1169_);
v_numMotives_1170_ = lean_ctor_get(v_val_1165_, 4);
lean_inc(v_numMotives_1170_);
v_numMinors_1171_ = lean_ctor_get(v_val_1165_, 5);
lean_inc(v_numMinors_1171_);
lean_dec_ref(v_val_1165_);
v_levelParams_1172_ = lean_ctor_get(v_toConstantVal_1169_, 1);
lean_inc_n(v_levelParams_1172_, 2);
v_type_1173_ = lean_ctor_get(v_toConstantVal_1169_, 2);
lean_inc_ref(v_type_1173_);
lean_dec_ref(v_toConstantVal_1169_);
v___x_1174_ = lean_box(0);
v___x_1175_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1172_, v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 1)
{
lean_object* v_head_1176_; lean_object* v_tail_1177_; lean_object* v___f_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v_head_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_head_1176_);
v_tail_1177_ = lean_ctor_get(v___x_1175_, 1);
lean_inc(v_tail_1177_);
lean_dec_ref_known(v___x_1175_, 2);
v___f_1178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1178_, 0, v_nParams_1155_);
lean_closure_set(v___f_1178_, 1, v_numMotives_1170_);
lean_closure_set(v___f_1178_, 2, v_numMinors_1171_);
lean_closure_set(v___f_1178_, 3, v___x_1162_);
lean_closure_set(v___f_1178_, 4, v_head_1176_);
lean_closure_set(v___f_1178_, 5, v_tail_1177_);
lean_closure_set(v___f_1178_, 6, v_recName_1154_);
lean_closure_set(v___f_1178_, 7, v_belowName_1156_);
lean_closure_set(v___f_1178_, 8, v_levelParams_1172_);
v___x_1179_ = 0;
v___x_1180_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1173_, v___f_1178_, v___x_1179_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_n(v_a_1181_, 2);
lean_dec_ref_known(v___x_1180_, 1);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 1);
lean_ctor_set(v___x_1167_, 0, v_a_1181_);
v___x_1183_ = v___x_1167_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1181_);
v___x_1183_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_addDecl(v___x_1183_, v___x_1179_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_toConstantVal_1185_; lean_object* v_name_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref_known(v___x_1184_, 1);
v_toConstantVal_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_toConstantVal_1185_);
lean_dec(v_a_1181_);
v_name_1186_ = lean_ctor_get(v_toConstantVal_1185_, 0);
lean_inc_n(v_name_1186_, 2);
lean_dec_ref(v_toConstantVal_1185_);
v___x_1187_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1186_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1266_);
v___x_1189_ = v___x_1187_;
v_isShared_1190_ = v_isSharedCheck_1265_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1265_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v_nextMacroScope_1193_; lean_object* v_ngen_1194_; lean_object* v_auxDeclNGen_1195_; lean_object* v_traceState_1196_; lean_object* v_recordedDeps_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1263_; 
v___x_1191_ = lean_st_ref_take(v_a_1160_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1193_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1194_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1195_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1196_ = lean_ctor_get(v___x_1191_, 4);
v_recordedDeps_1197_ = lean_ctor_get(v___x_1191_, 6);
v_messages_1198_ = lean_ctor_get(v___x_1191_, 7);
v_infoState_1199_ = lean_ctor_get(v___x_1191_, 8);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1191_, 9);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1264_);
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1263_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_recordedDeps_1197_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1195_);
lean_inc(v_ngen_1194_);
lean_inc(v_nextMacroScope_1193_);
lean_inc(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1263_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_inc(v_name_1186_);
v___x_1204_ = l_Lean_markAuxRecursor(v_env_1192_, v_name_1186_);
v___x_1205_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 5, v___x_1205_);
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_nextMacroScope_1193_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v_ngen_1194_);
lean_ctor_set(v_reuseFailAlloc_1262_, 3, v_auxDeclNGen_1195_);
lean_ctor_set(v_reuseFailAlloc_1262_, 4, v_traceState_1196_);
lean_ctor_set(v_reuseFailAlloc_1262_, 5, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1262_, 6, v_recordedDeps_1197_);
lean_ctor_set(v_reuseFailAlloc_1262_, 7, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1262_, 8, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1262_, 9, v_snapshotTasks_1200_);
v___x_1207_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_mctx_1210_; lean_object* v_zetaDeltaFVarIds_1211_; lean_object* v_postponed_1212_; lean_object* v_diag_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1260_; 
v___x_1208_ = lean_st_ref_put(v_a_1160_, v___x_1207_);
v___x_1209_ = lean_st_ref_take(v_a_1158_);
v_mctx_1210_ = lean_ctor_get(v___x_1209_, 0);
v_zetaDeltaFVarIds_1211_ = lean_ctor_get(v___x_1209_, 2);
v_postponed_1212_ = lean_ctor_get(v___x_1209_, 3);
v_diag_1213_ = lean_ctor_get(v___x_1209_, 4);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1209_, 1);
lean_dec(v_unused_1261_);
v___x_1215_ = v___x_1209_;
v_isShared_1216_ = v_isSharedCheck_1260_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_diag_1213_);
lean_inc(v_postponed_1212_);
lean_inc(v_zetaDeltaFVarIds_1211_);
lean_inc(v_mctx_1210_);
lean_dec(v___x_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1260_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 1, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_mctx_1210_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_zetaDeltaFVarIds_1211_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_postponed_1212_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_diag_1213_);
v___x_1219_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v_env_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v_ngen_1224_; lean_object* v_auxDeclNGen_1225_; lean_object* v_traceState_1226_; lean_object* v_recordedDeps_1227_; lean_object* v_messages_1228_; lean_object* v_infoState_1229_; lean_object* v_snapshotTasks_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1257_; 
v___x_1220_ = lean_st_ref_put(v_a_1158_, v___x_1219_);
v___x_1221_ = lean_st_ref_take(v_a_1160_);
v_env_1222_ = lean_ctor_get(v___x_1221_, 0);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1221_, 1);
v_ngen_1224_ = lean_ctor_get(v___x_1221_, 2);
v_auxDeclNGen_1225_ = lean_ctor_get(v___x_1221_, 3);
v_traceState_1226_ = lean_ctor_get(v___x_1221_, 4);
v_recordedDeps_1227_ = lean_ctor_get(v___x_1221_, 6);
v_messages_1228_ = lean_ctor_get(v___x_1221_, 7);
v_infoState_1229_ = lean_ctor_get(v___x_1221_, 8);
v_snapshotTasks_1230_ = lean_ctor_get(v___x_1221_, 9);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1221_, 5);
lean_dec(v_unused_1258_);
v___x_1232_ = v___x_1221_;
v_isShared_1233_ = v_isSharedCheck_1257_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snapshotTasks_1230_);
lean_inc(v_infoState_1229_);
lean_inc(v_messages_1228_);
lean_inc(v_recordedDeps_1227_);
lean_inc(v_traceState_1226_);
lean_inc(v_auxDeclNGen_1225_);
lean_inc(v_ngen_1224_);
lean_inc(v_nextMacroScope_1223_);
lean_inc(v_env_1222_);
lean_dec(v___x_1221_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1257_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = l_Lean_addProtected(v_env_1222_, v_name_1186_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 5, v___x_1205_);
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_nextMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_ngen_1224_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_auxDeclNGen_1225_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_traceState_1226_);
lean_ctor_set(v_reuseFailAlloc_1256_, 5, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1256_, 6, v_recordedDeps_1227_);
lean_ctor_set(v_reuseFailAlloc_1256_, 7, v_messages_1228_);
lean_ctor_set(v_reuseFailAlloc_1256_, 8, v_infoState_1229_);
lean_ctor_set(v_reuseFailAlloc_1256_, 9, v_snapshotTasks_1230_);
v___x_1236_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_mctx_1239_; lean_object* v_zetaDeltaFVarIds_1240_; lean_object* v_postponed_1241_; lean_object* v_diag_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1254_; 
v___x_1237_ = lean_st_ref_put(v_a_1160_, v___x_1236_);
v___x_1238_ = lean_st_ref_take(v_a_1158_);
v_mctx_1239_ = lean_ctor_get(v___x_1238_, 0);
v_zetaDeltaFVarIds_1240_ = lean_ctor_get(v___x_1238_, 2);
v_postponed_1241_ = lean_ctor_get(v___x_1238_, 3);
v_diag_1242_ = lean_ctor_get(v___x_1238_, 4);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1238_, 1);
lean_dec(v_unused_1255_);
v___x_1244_ = v___x_1238_;
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_diag_1242_);
lean_inc(v_postponed_1241_);
lean_inc(v_zetaDeltaFVarIds_1240_);
lean_inc(v_mctx_1239_);
lean_dec(v___x_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1254_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_box(0);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1217_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_mctx_1239_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_zetaDeltaFVarIds_1240_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_postponed_1241_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v_diag_1242_);
v___x_1248_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_st_ref_put(v_a_1158_, v___x_1248_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1246_);
v___x_1251_ = v___x_1189_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
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
lean_dec(v_a_1181_);
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_del_object(v___x_1167_);
v_a_1268_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1180_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1180_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v___x_1175_);
lean_dec_ref(v_type_1173_);
lean_dec(v_levelParams_1172_);
lean_dec(v_numMinors_1171_);
lean_dec(v_numMotives_1170_);
lean_del_object(v___x_1167_);
lean_dec(v_belowName_1156_);
lean_dec(v_nParams_1155_);
v___x_1276_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1277_ = l_Lean_MessageData_ofName(v_recName_1154_);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1280_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1281_;
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_a_1164_);
lean_dec(v_belowName_1156_);
lean_dec(v_nParams_1155_);
v___x_1283_ = l_Lean_MessageData_ofName(v_recName_1154_);
v___x_1284_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1285_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
return v___x_1286_;
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec(v_belowName_1156_);
lean_dec(v_nParams_1155_);
lean_dec(v_recName_1154_);
v_a_1287_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1163_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1163_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1295_, lean_object* v_nParams_1296_, lean_object* v_belowName_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1295_, v_nParams_1296_, v_belowName_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1304_, lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1312_, lean_object* v_msg_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1312_, v_msg_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1320_, uint8_t v_s_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1320_, v_s_1321_, v___y_1323_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1328_, lean_object* v_s_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v_s_boxed_1335_; lean_object* v_res_1336_; 
v_s_boxed_1335_ = lean_unbox(v_s_1329_);
v_res_1336_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1328_, v_s_boxed_1335_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1336_;
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1353_, lean_object* v_ref_1354_, lean_object* v_constName_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1354_, v_constName_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_ref_1363_, lean_object* v_constName_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1362_, v_ref_1363_, v_constName_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v_ref_1363_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1371_, lean_object* v_ref_1372_, lean_object* v_msg_1373_, lean_object* v_declHint_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1372_, v_msg_1373_, v_declHint_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_ref_1382_, lean_object* v_msg_1383_, lean_object* v_declHint_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1381_, v_ref_1382_, v_msg_1383_, v_declHint_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v_ref_1382_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1391_, lean_object* v_declHint_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1391_, v_declHint_1392_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1399_, lean_object* v_declHint_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1399_, v_declHint_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1407_, lean_object* v_ref_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1408_, v_msg_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ref_1417_, lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1416_, v_ref_1417_, v_msg_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v_ref_1417_);
return v_res_1424_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_unsigned_to_nat(32u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1428_ = ((size_t)5ULL);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_unsigned_to_nat(32u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1433_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1429_);
lean_ctor_set(v___x_1433_, 3, v___x_1429_);
lean_ctor_set_usize(v___x_1433_, 4, v___x_1428_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v_traceState_1437_; lean_object* v_traces_1438_; lean_object* v___x_1439_; lean_object* v_traceState_1440_; lean_object* v_env_1441_; lean_object* v_nextMacroScope_1442_; lean_object* v_ngen_1443_; lean_object* v_auxDeclNGen_1444_; lean_object* v_cache_1445_; lean_object* v_recordedDeps_1446_; lean_object* v_messages_1447_; lean_object* v_infoState_1448_; lean_object* v_snapshotTasks_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1468_; 
v___x_1436_ = lean_st_ref_get(v___y_1434_);
v_traceState_1437_ = lean_ctor_get(v___x_1436_, 4);
lean_inc_ref(v_traceState_1437_);
lean_dec(v___x_1436_);
v_traces_1438_ = lean_ctor_get(v_traceState_1437_, 0);
lean_inc_ref(v_traces_1438_);
lean_dec_ref(v_traceState_1437_);
v___x_1439_ = lean_st_ref_take(v___y_1434_);
v_traceState_1440_ = lean_ctor_get(v___x_1439_, 4);
v_env_1441_ = lean_ctor_get(v___x_1439_, 0);
v_nextMacroScope_1442_ = lean_ctor_get(v___x_1439_, 1);
v_ngen_1443_ = lean_ctor_get(v___x_1439_, 2);
v_auxDeclNGen_1444_ = lean_ctor_get(v___x_1439_, 3);
v_cache_1445_ = lean_ctor_get(v___x_1439_, 5);
v_recordedDeps_1446_ = lean_ctor_get(v___x_1439_, 6);
v_messages_1447_ = lean_ctor_get(v___x_1439_, 7);
v_infoState_1448_ = lean_ctor_get(v___x_1439_, 8);
v_snapshotTasks_1449_ = lean_ctor_get(v___x_1439_, 9);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1451_ = v___x_1439_;
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snapshotTasks_1449_);
lean_inc(v_infoState_1448_);
lean_inc(v_messages_1447_);
lean_inc(v_recordedDeps_1446_);
lean_inc(v_cache_1445_);
lean_inc(v_traceState_1440_);
lean_inc(v_auxDeclNGen_1444_);
lean_inc(v_ngen_1443_);
lean_inc(v_nextMacroScope_1442_);
lean_inc(v_env_1441_);
lean_dec(v___x_1439_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
uint64_t v_tid_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1466_; 
v_tid_1453_ = lean_ctor_get_uint64(v_traceState_1440_, sizeof(void*)*1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_traceState_1440_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_traceState_1440_, 0);
lean_dec(v_unused_1467_);
v___x_1455_ = v_traceState_1440_;
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_traceState_1440_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1457_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1457_);
lean_ctor_set_uint64(v_reuseFailAlloc_1465_, sizeof(void*)*1, v_tid_1453_);
v___x_1459_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v___x_1459_);
v___x_1461_ = v___x_1451_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_env_1441_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v_cache_1445_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_recordedDeps_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_messages_1447_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_infoState_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 9, v_snapshotTasks_1449_);
v___x_1461_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_st_ref_put(v___y_1434_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_traces_1438_);
return v___x_1463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1469_);
lean_dec(v___y_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1484_, lean_object* v_opt_1485_){
_start:
{
lean_object* v_name_1486_; lean_object* v_defValue_1487_; lean_object* v_map_1488_; lean_object* v___x_1489_; 
v_name_1486_ = lean_ctor_get(v_opt_1485_, 0);
v_defValue_1487_ = lean_ctor_get(v_opt_1485_, 1);
v_map_1488_ = lean_ctor_get(v_opts_1484_, 0);
v___x_1489_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1488_, v_name_1486_);
if (lean_obj_tag(v___x_1489_) == 0)
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_unbox(v_defValue_1487_);
return v___x_1490_;
}
else
{
lean_object* v_val_1491_; 
v_val_1491_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___x_1489_, 1);
if (lean_obj_tag(v_val_1491_) == 1)
{
uint8_t v_v_1492_; 
v_v_1492_ = lean_ctor_get_uint8(v_val_1491_, 0);
lean_dec_ref_known(v_val_1491_, 0);
return v_v_1492_;
}
else
{
uint8_t v___x_1493_; 
lean_dec(v_val_1491_);
v___x_1493_ = lean_unbox(v_defValue_1487_);
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1494_, lean_object* v_opt_1495_){
_start:
{
uint8_t v_res_1496_; lean_object* v_r_1497_; 
v_res_1496_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1494_, v_opt_1495_);
lean_dec_ref(v_opt_1495_);
lean_dec_ref(v_opts_1494_);
v_r_1497_ = lean_box(v_res_1496_);
return v_r_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1498_, lean_object* v_x_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = l_Lean_MessageData_ofName(v_indName_1498_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_mkBelow___lam__0(v_indName_1507_, v_x_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec_ref(v_x_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1515_){
_start:
{
if (lean_obj_tag(v_e_1515_) == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = 2;
return v___x_1516_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = 0;
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1518_);
lean_dec_ref(v_e_1518_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v_x_1521_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v_x_1521_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set_tag(v___x_1525_, 1);
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_a_1531_ = lean_ctor_get(v_x_1521_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1521_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v_x_1521_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v_x_1521_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set_tag(v___x_1533_, 0);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1542_, lean_object* v_opt_1543_){
_start:
{
lean_object* v_name_1544_; lean_object* v_defValue_1545_; lean_object* v_map_1546_; lean_object* v___x_1547_; 
v_name_1544_ = lean_ctor_get(v_opt_1543_, 0);
v_defValue_1545_ = lean_ctor_get(v_opt_1543_, 1);
v_map_1546_ = lean_ctor_get(v_opts_1542_, 0);
v___x_1547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1546_, v_name_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_inc(v_defValue_1545_);
return v_defValue_1545_;
}
else
{
lean_object* v_val_1548_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1547_, 1);
if (lean_obj_tag(v_val_1548_) == 3)
{
lean_object* v_v_1549_; 
v_v_1549_ = lean_ctor_get(v_val_1548_, 0);
lean_inc(v_v_1549_);
lean_dec_ref_known(v_val_1548_, 1);
return v_v_1549_;
}
else
{
lean_dec(v_val_1548_);
lean_inc(v_defValue_1545_);
return v_defValue_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1550_, lean_object* v_opt_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1550_, v_opt_1551_);
lean_dec_ref(v_opt_1551_);
lean_dec_ref(v_opts_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_bs_1555_){
_start:
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_usize_dec_lt(v_i_1554_, v_sz_1553_);
if (v___x_1556_ == 0)
{
return v_bs_1555_;
}
else
{
lean_object* v_v_1557_; lean_object* v_msg_1558_; lean_object* v___x_1559_; lean_object* v_bs_x27_1560_; size_t v___x_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_v_1557_ = lean_array_uget_borrowed(v_bs_1555_, v_i_1554_);
v_msg_1558_ = lean_ctor_get(v_v_1557_, 1);
lean_inc_ref(v_msg_1558_);
v___x_1559_ = lean_unsigned_to_nat(0u);
v_bs_x27_1560_ = lean_array_uset(v_bs_1555_, v_i_1554_, v___x_1559_);
v___x_1561_ = ((size_t)1ULL);
v___x_1562_ = lean_usize_add(v_i_1554_, v___x_1561_);
v___x_1563_ = lean_array_uset(v_bs_x27_1560_, v_i_1554_, v_msg_1558_);
v_i_1554_ = v___x_1562_;
v_bs_1555_ = v___x_1563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_bs_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1571_, lean_object* v_data_1572_, lean_object* v_ref_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_toCold_1580_; lean_object* v_currRecDepth_1581_; lean_object* v_ref_1582_; uint16_t v_optionFlags_1583_; uint8_t v_suppressElabErrors_1584_; uint8_t v_isRecordingDeps_1585_; lean_object* v_ref_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_traceState_1589_; lean_object* v_traces_1590_; lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; lean_object* v_msg_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1635_; 
v_toCold_1580_ = lean_ctor_get(v___y_1577_, 0);
v_currRecDepth_1581_ = lean_ctor_get(v___y_1577_, 1);
v_ref_1582_ = lean_ctor_get(v___y_1577_, 2);
v_optionFlags_1583_ = lean_ctor_get_uint16(v___y_1577_, sizeof(void*)*3);
v_suppressElabErrors_1584_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1585_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*3 + 3);
v_ref_1586_ = l_Lean_replaceRef(v_ref_1573_, v_ref_1582_);
lean_inc(v_currRecDepth_1581_);
lean_inc_ref(v_toCold_1580_);
v___x_1587_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1587_, 0, v_toCold_1580_);
lean_ctor_set(v___x_1587_, 1, v_currRecDepth_1581_);
lean_ctor_set(v___x_1587_, 2, v_ref_1586_);
lean_ctor_set_uint16(v___x_1587_, sizeof(void*)*3, v_optionFlags_1583_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*3 + 2, v_suppressElabErrors_1584_);
lean_ctor_set_uint8(v___x_1587_, sizeof(void*)*3 + 3, v_isRecordingDeps_1585_);
v___x_1588_ = lean_st_ref_get(v___y_1578_);
v_traceState_1589_ = lean_ctor_get(v___x_1588_, 4);
lean_inc_ref(v_traceState_1589_);
lean_dec(v___x_1588_);
v_traces_1590_ = lean_ctor_get(v_traceState_1589_, 0);
lean_inc_ref(v_traces_1590_);
lean_dec_ref(v_traceState_1589_);
v___x_1591_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1590_);
lean_dec_ref(v_traces_1590_);
v_sz_1592_ = lean_array_size(v___x_1591_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1592_, v___x_1593_, v___x_1591_);
v_msg_1595_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1595_, 0, v_data_1572_);
lean_ctor_set(v_msg_1595_, 1, v_msg_1574_);
lean_ctor_set(v_msg_1595_, 2, v___x_1594_);
v___x_1596_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1595_, v___y_1575_, v___y_1576_, v___x_1587_, v___y_1578_);
lean_dec_ref_known(v___x_1587_, 3);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1635_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1635_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v_traceState_1602_; lean_object* v_env_1603_; lean_object* v_nextMacroScope_1604_; lean_object* v_ngen_1605_; lean_object* v_auxDeclNGen_1606_; lean_object* v_cache_1607_; lean_object* v_recordedDeps_1608_; lean_object* v_messages_1609_; lean_object* v_infoState_1610_; lean_object* v_snapshotTasks_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1634_; 
v___x_1601_ = lean_st_ref_take(v___y_1578_);
v_traceState_1602_ = lean_ctor_get(v___x_1601_, 4);
v_env_1603_ = lean_ctor_get(v___x_1601_, 0);
v_nextMacroScope_1604_ = lean_ctor_get(v___x_1601_, 1);
v_ngen_1605_ = lean_ctor_get(v___x_1601_, 2);
v_auxDeclNGen_1606_ = lean_ctor_get(v___x_1601_, 3);
v_cache_1607_ = lean_ctor_get(v___x_1601_, 5);
v_recordedDeps_1608_ = lean_ctor_get(v___x_1601_, 6);
v_messages_1609_ = lean_ctor_get(v___x_1601_, 7);
v_infoState_1610_ = lean_ctor_get(v___x_1601_, 8);
v_snapshotTasks_1611_ = lean_ctor_get(v___x_1601_, 9);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1634_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_snapshotTasks_1611_);
lean_inc(v_infoState_1610_);
lean_inc(v_messages_1609_);
lean_inc(v_recordedDeps_1608_);
lean_inc(v_cache_1607_);
lean_inc(v_traceState_1602_);
lean_inc(v_auxDeclNGen_1606_);
lean_inc(v_ngen_1605_);
lean_inc(v_nextMacroScope_1604_);
lean_inc(v_env_1603_);
lean_dec(v___x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1634_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
uint64_t v_tid_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1632_; 
v_tid_1615_ = lean_ctor_get_uint64(v_traceState_1602_, sizeof(void*)*1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_traceState_1602_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v_traceState_1602_, 0);
lean_dec(v_unused_1633_);
v___x_1617_ = v_traceState_1602_;
v_isShared_1618_ = v_isSharedCheck_1632_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v_traceState_1602_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1632_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_ref_1573_);
lean_ctor_set(v___x_1620_, 1, v_a_1597_);
v___x_1621_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1571_, v___x_1620_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1621_);
v___x_1623_ = v___x_1617_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1621_);
lean_ctor_set_uint64(v_reuseFailAlloc_1631_, sizeof(void*)*1, v_tid_1615_);
v___x_1623_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___x_1623_);
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_env_1603_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_nextMacroScope_1604_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_ngen_1605_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_auxDeclNGen_1606_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_cache_1607_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_recordedDeps_1608_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_messages_1609_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_infoState_1610_);
lean_ctor_set(v_reuseFailAlloc_1630_, 9, v_snapshotTasks_1611_);
v___x_1625_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_st_ref_put(v___y_1578_, v___x_1625_);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1619_);
v___x_1628_ = v___x_1599_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1619_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1636_, lean_object* v_data_1637_, lean_object* v_ref_1638_, lean_object* v_msg_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1636_, v_data_1637_, v_ref_1638_, v_msg_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1646_; double v___x_1647_; 
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_float_of_nat(v___x_1646_);
return v___x_1647_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1651_; double v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(1000u);
v___x_1652_ = lean_float_of_nat(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1653_, uint8_t v_collapsed_1654_, lean_object* v_tag_1655_, lean_object* v_opts_1656_, uint8_t v_clsEnabled_1657_, lean_object* v_oldTraces_1658_, lean_object* v_msg_1659_, lean_object* v_resStartStop_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v_data_1671_; lean_object* v_fst_1674_; lean_object* v_snd_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___y_1679_; lean_object* v_a_1680_; uint8_t v___y_1695_; double v___y_1727_; 
v_fst_1666_ = lean_ctor_get(v_resStartStop_1660_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_resStartStop_1660_, 1);
lean_inc(v_snd_1667_);
lean_dec_ref(v_resStartStop_1660_);
v_fst_1674_ = lean_ctor_get(v_snd_1667_, 0);
lean_inc(v_fst_1674_);
v_snd_1675_ = lean_ctor_get(v_snd_1667_, 1);
lean_inc(v_snd_1675_);
lean_dec(v_snd_1667_);
v___x_1676_ = l_Lean_trace_profiler;
v___x_1677_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1656_, v___x_1676_);
if (v___x_1677_ == 0)
{
v___y_1695_ = v___x_1677_;
goto v___jp_1694_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1733_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1656_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; double v___x_1736_; double v___x_1737_; double v___x_1738_; 
v___x_1734_ = l_Lean_trace_profiler_threshold;
v___x_1735_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1656_, v___x_1734_);
v___x_1736_ = lean_float_of_nat(v___x_1735_);
v___x_1737_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1738_ = lean_float_div(v___x_1736_, v___x_1737_);
v___y_1727_ = v___x_1738_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; double v___x_1741_; 
v___x_1739_ = l_Lean_trace_profiler_threshold;
v___x_1740_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1656_, v___x_1739_);
v___x_1741_ = lean_float_of_nat(v___x_1740_);
v___y_1727_ = v___x_1741_;
goto v___jp_1726_;
}
}
v___jp_1668_:
{
lean_object* v___x_1672_; 
lean_inc(v___y_1669_);
v___x_1672_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1658_, v_data_1671_, v___y_1669_, v___y_1670_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v___x_1673_; 
lean_dec_ref_known(v___x_1672_, 1);
v___x_1673_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1666_);
return v___x_1673_;
}
else
{
lean_dec(v_fst_1666_);
return v___x_1672_;
}
}
v___jp_1678_:
{
uint8_t v_result_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; double v___x_1684_; lean_object* v_data_1685_; 
v_result_1681_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1666_);
v___x_1682_ = lean_box(v_result_1681_);
v___x_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
v___x_1684_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1655_);
lean_inc_ref(v___x_1683_);
lean_inc(v_cls_1653_);
v_data_1685_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1685_, 0, v_cls_1653_);
lean_ctor_set(v_data_1685_, 1, v___x_1683_);
lean_ctor_set(v_data_1685_, 2, v_tag_1655_);
lean_ctor_set_float(v_data_1685_, sizeof(void*)*3, v___x_1684_);
lean_ctor_set_float(v_data_1685_, sizeof(void*)*3 + 8, v___x_1684_);
lean_ctor_set_uint8(v_data_1685_, sizeof(void*)*3 + 16, v_collapsed_1654_);
if (v___x_1677_ == 0)
{
lean_dec_ref_known(v___x_1683_, 1);
lean_dec(v_snd_1675_);
lean_dec(v_fst_1674_);
lean_dec_ref(v_tag_1655_);
lean_dec(v_cls_1653_);
v___y_1669_ = v___y_1679_;
v___y_1670_ = v_a_1680_;
v_data_1671_ = v_data_1685_;
goto v___jp_1668_;
}
else
{
lean_object* v_data_1686_; double v___x_1687_; double v___x_1688_; 
lean_dec_ref_known(v_data_1685_, 3);
v_data_1686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1686_, 0, v_cls_1653_);
lean_ctor_set(v_data_1686_, 1, v___x_1683_);
lean_ctor_set(v_data_1686_, 2, v_tag_1655_);
v___x_1687_ = lean_unbox_float(v_fst_1674_);
lean_dec(v_fst_1674_);
lean_ctor_set_float(v_data_1686_, sizeof(void*)*3, v___x_1687_);
v___x_1688_ = lean_unbox_float(v_snd_1675_);
lean_dec(v_snd_1675_);
lean_ctor_set_float(v_data_1686_, sizeof(void*)*3 + 8, v___x_1688_);
lean_ctor_set_uint8(v_data_1686_, sizeof(void*)*3 + 16, v_collapsed_1654_);
v___y_1669_ = v___y_1679_;
v___y_1670_ = v_a_1680_;
v_data_1671_ = v_data_1686_;
goto v___jp_1668_;
}
}
v___jp_1689_:
{
lean_object* v_ref_1690_; lean_object* v___x_1691_; 
v_ref_1690_ = lean_ctor_get(v___y_1663_, 2);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
lean_inc(v___y_1662_);
lean_inc_ref(v___y_1661_);
lean_inc(v_fst_1666_);
v___x_1691_ = lean_apply_6(v_msg_1659_, v_fst_1666_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, lean_box(0));
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___y_1679_ = v_ref_1690_;
v_a_1680_ = v_a_1692_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1693_; 
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1679_ = v_ref_1690_;
v_a_1680_ = v___x_1693_;
goto v___jp_1678_;
}
}
v___jp_1694_:
{
if (v_clsEnabled_1657_ == 0)
{
if (v___y_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v_traceState_1697_; lean_object* v_env_1698_; lean_object* v_nextMacroScope_1699_; lean_object* v_ngen_1700_; lean_object* v_auxDeclNGen_1701_; lean_object* v_cache_1702_; lean_object* v_recordedDeps_1703_; lean_object* v_messages_1704_; lean_object* v_infoState_1705_; lean_object* v_snapshotTasks_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_snd_1675_);
lean_dec(v_fst_1674_);
lean_dec_ref(v_msg_1659_);
lean_dec_ref(v_tag_1655_);
lean_dec(v_cls_1653_);
v___x_1696_ = lean_st_ref_take(v___y_1664_);
v_traceState_1697_ = lean_ctor_get(v___x_1696_, 4);
v_env_1698_ = lean_ctor_get(v___x_1696_, 0);
v_nextMacroScope_1699_ = lean_ctor_get(v___x_1696_, 1);
v_ngen_1700_ = lean_ctor_get(v___x_1696_, 2);
v_auxDeclNGen_1701_ = lean_ctor_get(v___x_1696_, 3);
v_cache_1702_ = lean_ctor_get(v___x_1696_, 5);
v_recordedDeps_1703_ = lean_ctor_get(v___x_1696_, 6);
v_messages_1704_ = lean_ctor_get(v___x_1696_, 7);
v_infoState_1705_ = lean_ctor_get(v___x_1696_, 8);
v_snapshotTasks_1706_ = lean_ctor_get(v___x_1696_, 9);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1708_ = v___x_1696_;
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snapshotTasks_1706_);
lean_inc(v_infoState_1705_);
lean_inc(v_messages_1704_);
lean_inc(v_recordedDeps_1703_);
lean_inc(v_cache_1702_);
lean_inc(v_traceState_1697_);
lean_inc(v_auxDeclNGen_1701_);
lean_inc(v_ngen_1700_);
lean_inc(v_nextMacroScope_1699_);
lean_inc(v_env_1698_);
lean_dec(v___x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1725_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
uint64_t v_tid_1710_; lean_object* v_traces_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1724_; 
v_tid_1710_ = lean_ctor_get_uint64(v_traceState_1697_, sizeof(void*)*1);
v_traces_1711_ = lean_ctor_get(v_traceState_1697_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_traceState_1697_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1713_ = v_traceState_1697_;
v_isShared_1714_ = v_isSharedCheck_1724_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_traces_1711_);
lean_dec(v_traceState_1697_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1724_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1658_, v_traces_1711_);
lean_dec_ref(v_traces_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1715_);
lean_ctor_set_uint64(v_reuseFailAlloc_1723_, sizeof(void*)*1, v_tid_1710_);
v___x_1717_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 4, v___x_1717_);
v___x_1719_ = v___x_1708_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_env_1698_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_nextMacroScope_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_ngen_1700_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_auxDeclNGen_1701_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_cache_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_recordedDeps_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_messages_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_infoState_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v_snapshotTasks_1706_);
v___x_1719_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_st_ref_put(v___y_1664_, v___x_1719_);
v___x_1721_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1666_);
return v___x_1721_;
}
}
}
}
}
else
{
goto v___jp_1689_;
}
}
else
{
goto v___jp_1689_;
}
}
v___jp_1726_:
{
double v___x_1728_; double v___x_1729_; double v___x_1730_; uint8_t v___x_1731_; 
v___x_1728_ = lean_unbox_float(v_snd_1675_);
v___x_1729_ = lean_unbox_float(v_fst_1674_);
v___x_1730_ = lean_float_sub(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_float_decLt(v___y_1727_, v___x_1730_);
v___y_1695_ = v___x_1731_;
goto v___jp_1694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1742_, lean_object* v_collapsed_1743_, lean_object* v_tag_1744_, lean_object* v_opts_1745_, lean_object* v_clsEnabled_1746_, lean_object* v_oldTraces_1747_, lean_object* v_msg_1748_, lean_object* v_resStartStop_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v_collapsed_boxed_1755_; uint8_t v_clsEnabled_boxed_1756_; lean_object* v_res_1757_; 
v_collapsed_boxed_1755_ = lean_unbox(v_collapsed_1743_);
v_clsEnabled_boxed_1756_ = lean_unbox(v_clsEnabled_1746_);
v_res_1757_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1742_, v_collapsed_boxed_1755_, v_tag_1744_, v_opts_1745_, v_clsEnabled_boxed_1756_, v_oldTraces_1747_, v_msg_1748_, v_resStartStop_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec_ref(v_opts_1745_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1758_, lean_object* v___x_1759_, lean_object* v___x_1760_, lean_object* v___x_1761_, lean_object* v_a_1762_, lean_object* v_b_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_nat_dec_lt(v_a_1762_, v_upperBound_1758_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec(v_a_1762_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v___x_1759_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_b_1763_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = lean_box(0);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_a_1762_, v___x_1772_);
lean_dec(v_a_1762_);
lean_inc_n(v___x_1773_, 2);
lean_inc(v___x_1759_);
v___x_1774_ = lean_name_append_index_after(v___x_1759_, v___x_1773_);
lean_inc(v___x_1760_);
v___x_1775_ = lean_name_append_index_after(v___x_1760_, v___x_1773_);
lean_inc(v___x_1761_);
v___x_1776_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1774_, v___x_1761_, v___x_1775_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_dec_ref_known(v___x_1776_, 1);
v_a_1762_ = v___x_1773_;
v_b_1763_ = v___x_1771_;
goto _start;
}
else
{
lean_dec(v___x_1773_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
lean_dec(v___x_1759_);
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v___x_1781_, lean_object* v_a_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1778_, v___x_1779_, v___x_1780_, v___x_1781_, v_a_1782_, v_b_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v_upperBound_1778_);
return v_res_1789_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1800_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1801_ = l_Lean_Name_append(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1802_; double v___x_1803_; 
v___x_1802_ = lean_unsigned_to_nat(1000000000u);
v___x_1803_ = lean_float_of_nat(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_toCold_1810_; lean_object* v_options_1811_; lean_object* v_inheritedTraceOptions_1812_; uint8_t v_hasTrace_1813_; lean_object* v___x_1814_; 
v_toCold_1810_ = lean_ctor_get(v_a_1807_, 0);
v_options_1811_ = lean_ctor_get(v_toCold_1810_, 2);
v_inheritedTraceOptions_1812_ = lean_ctor_get(v_toCold_1810_, 11);
v_hasTrace_1813_ = lean_ctor_get_uint8(v_options_1811_, sizeof(void*)*1);
v___x_1814_ = lean_box(0);
if (v_hasTrace_1813_ == 0)
{
lean_object* v___x_1815_; 
lean_inc(v_indName_1804_);
v___x_1815_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1879_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1879_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1879_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
if (lean_obj_tag(v_a_1816_) == 5)
{
lean_object* v_val_1820_; uint8_t v_isRec_1821_; 
v_val_1820_ = lean_ctor_get(v_a_1816_, 0);
lean_inc_ref(v_val_1820_);
lean_dec_ref_known(v_a_1816_, 1);
v_isRec_1821_ = lean_ctor_get_uint8(v_val_1820_, sizeof(void*)*6);
if (v_isRec_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_dec_ref(v_val_1820_);
lean_dec(v_indName_1804_);
v___x_1822_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1822_);
v___x_1824_ = v___x_1818_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
else
{
lean_object* v_toConstantVal_1826_; lean_object* v_numParams_1827_; lean_object* v_all_1828_; lean_object* v_numNested_1829_; lean_object* v_type_1830_; lean_object* v___x_1831_; 
lean_del_object(v___x_1818_);
v_toConstantVal_1826_ = lean_ctor_get(v_val_1820_, 0);
lean_inc_ref(v_toConstantVal_1826_);
v_numParams_1827_ = lean_ctor_get(v_val_1820_, 1);
lean_inc(v_numParams_1827_);
v_all_1828_ = lean_ctor_get(v_val_1820_, 3);
lean_inc(v_all_1828_);
v_numNested_1829_ = lean_ctor_get(v_val_1820_, 5);
lean_inc(v_numNested_1829_);
lean_dec_ref(v_val_1820_);
v_type_1830_ = lean_ctor_get(v_toConstantVal_1826_, 2);
lean_inc_ref(v_type_1830_);
lean_dec_ref(v_toConstantVal_1826_);
v___x_1831_ = l_Lean_Meta_isPropFormerType(v_type_1830_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1866_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1834_ = v___x_1831_;
v_isShared_1835_ = v_isSharedCheck_1866_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1831_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1866_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; 
v___x_1836_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_del_object(v___x_1834_);
lean_inc_n(v_indName_1804_, 2);
v___x_1837_ = l_Lean_mkRecName(v_indName_1804_);
v___x_1838_ = l_Lean_mkBelowName(v_indName_1804_);
lean_inc(v___x_1838_);
lean_inc(v_numParams_1827_);
lean_inc(v___x_1837_);
v___x_1839_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1837_, v_numParams_1827_, v___x_1838_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1860_; 
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1839_, 0);
lean_dec(v_unused_1861_);
v___x_1841_ = v___x_1839_;
v_isShared_1842_ = v_isSharedCheck_1860_;
goto v_resetjp_1840_;
}
else
{
lean_dec(v___x_1839_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1860_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = l_List_get_x21Internal___redArg(v___x_1814_, v_all_1828_, v___x_1843_);
lean_dec(v_all_1828_);
v___x_1845_ = lean_name_eq(v___x_1844_, v_indName_1804_);
lean_dec(v_indName_1804_);
lean_dec(v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
lean_dec(v___x_1838_);
lean_dec(v___x_1837_);
lean_dec(v_numNested_1829_);
lean_dec(v_numParams_1827_);
v___x_1846_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1846_);
v___x_1848_ = v___x_1841_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
lean_del_object(v___x_1841_);
v___x_1850_ = lean_box(0);
v___x_1851_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1829_, v___x_1837_, v___x_1838_, v_numParams_1827_, v___x_1843_, v___x_1850_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_numNested_1829_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1859_);
v___x_1853_ = v___x_1851_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v___x_1851_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 0, v___x_1850_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1850_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
return v___x_1851_;
}
}
}
}
else
{
lean_dec(v___x_1838_);
lean_dec(v___x_1837_);
lean_dec(v_numNested_1829_);
lean_dec(v_all_1828_);
lean_dec(v_numParams_1827_);
lean_dec(v_indName_1804_);
return v___x_1839_;
}
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v_numNested_1829_);
lean_dec(v_all_1828_);
lean_dec(v_numParams_1827_);
lean_dec(v_indName_1804_);
v___x_1862_ = lean_box(0);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 0, v___x_1862_);
v___x_1864_ = v___x_1834_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v_numNested_1829_);
lean_dec(v_all_1828_);
lean_dec(v_numParams_1827_);
lean_dec(v_indName_1804_);
v_a_1867_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1831_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1831_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_dec(v_a_1816_);
lean_dec(v_indName_1804_);
v___x_1875_ = lean_box(0);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1875_);
v___x_1877_ = v___x_1818_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_indName_1804_);
v_a_1880_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1815_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1815_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v___f_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v_a_1896_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_a_1911_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v_a_1916_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_a_1921_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v_a_1933_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v_a_1938_; 
lean_inc(v_indName_1804_);
v___f_1888_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1888_, 0, v_indName_1804_);
v___x_1889_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1890_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1891_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1892_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1812_, v_options_1811_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = l_Lean_trace_profiler;
v___x_2004_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1811_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v___f_1888_);
lean_inc(v_indName_1804_);
v___x_2005_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2069_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2069_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2069_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
if (lean_obj_tag(v_a_2006_) == 5)
{
lean_object* v_val_2010_; uint8_t v_isRec_2011_; 
v_val_2010_ = lean_ctor_get(v_a_2006_, 0);
lean_inc_ref(v_val_2010_);
lean_dec_ref_known(v_a_2006_, 1);
v_isRec_2011_ = lean_ctor_get_uint8(v_val_2010_, sizeof(void*)*6);
if (v_isRec_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_dec_ref(v_val_2010_);
lean_dec(v_indName_1804_);
v___x_2012_ = lean_box(0);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2012_);
v___x_2014_ = v___x_2008_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
else
{
lean_object* v_toConstantVal_2016_; lean_object* v_numParams_2017_; lean_object* v_all_2018_; lean_object* v_numNested_2019_; lean_object* v_type_2020_; lean_object* v___x_2021_; 
lean_del_object(v___x_2008_);
v_toConstantVal_2016_ = lean_ctor_get(v_val_2010_, 0);
lean_inc_ref(v_toConstantVal_2016_);
v_numParams_2017_ = lean_ctor_get(v_val_2010_, 1);
lean_inc(v_numParams_2017_);
v_all_2018_ = lean_ctor_get(v_val_2010_, 3);
lean_inc(v_all_2018_);
v_numNested_2019_ = lean_ctor_get(v_val_2010_, 5);
lean_inc(v_numNested_2019_);
lean_dec_ref(v_val_2010_);
v_type_2020_ = lean_ctor_get(v_toConstantVal_2016_, 2);
lean_inc_ref(v_type_2020_);
lean_dec_ref(v_toConstantVal_2016_);
v___x_2021_ = l_Lean_Meta_isPropFormerType(v_type_2020_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2056_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2056_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2056_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_del_object(v___x_2024_);
lean_inc_n(v_indName_1804_, 2);
v___x_2027_ = l_Lean_mkRecName(v_indName_1804_);
v___x_2028_ = l_Lean_mkBelowName(v_indName_1804_);
lean_inc(v___x_2028_);
lean_inc(v_numParams_2017_);
lean_inc(v___x_2027_);
v___x_2029_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2027_, v_numParams_2017_, v___x_2028_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2050_; 
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2029_, 0);
lean_dec(v_unused_2051_);
v___x_2031_ = v___x_2029_;
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v___x_2029_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2050_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = l_List_get_x21Internal___redArg(v___x_1814_, v_all_2018_, v___x_2033_);
lean_dec(v_all_2018_);
v___x_2035_ = lean_name_eq(v___x_2034_, v_indName_1804_);
lean_dec(v_indName_1804_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
lean_dec(v___x_2028_);
lean_dec(v___x_2027_);
lean_dec(v_numNested_2019_);
lean_dec(v_numParams_2017_);
v___x_2036_ = lean_box(0);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2036_);
v___x_2038_ = v___x_2031_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_del_object(v___x_2031_);
v___x_2040_ = lean_box(0);
v___x_2041_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2019_, v___x_2027_, v___x_2028_, v_numParams_2017_, v___x_2033_, v___x_2040_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_numNested_2019_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v___x_2041_, 0);
lean_dec(v_unused_2049_);
v___x_2043_ = v___x_2041_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v___x_2041_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2040_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2040_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
return v___x_2041_;
}
}
}
}
else
{
lean_dec(v___x_2028_);
lean_dec(v___x_2027_);
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1804_);
return v___x_2029_;
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1804_);
v___x_2052_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2052_);
v___x_2054_ = v___x_2024_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_numNested_2019_);
lean_dec(v_all_2018_);
lean_dec(v_numParams_2017_);
lean_dec(v_indName_1804_);
v_a_2057_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2021_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2021_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_dec(v_a_2006_);
lean_dec(v_indName_1804_);
v___x_2065_ = lean_box(0);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2065_);
v___x_2067_ = v___x_2008_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_indName_1804_);
v_a_2070_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2005_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2005_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
else
{
goto v___jp_1940_;
}
}
else
{
goto v___jp_1940_;
}
v___jp_1893_:
{
lean_object* v___x_1897_; double v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1897_ = lean_io_mono_nanos_now();
v___x_1898_ = lean_float_of_nat(v___y_1894_);
v___x_1899_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1900_ = lean_float_div(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_float_of_nat(v___x_1897_);
v___x_1902_ = lean_float_div(v___x_1901_, v___x_1899_);
v___x_1903_ = lean_box_float(v___x_1900_);
v___x_1904_ = lean_box_float(v___x_1902_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_a_1896_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1889_, v_hasTrace_1813_, v___x_1890_, v_options_1811_, v___x_1892_, v___y_1895_, v___f_1888_, v___x_1906_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1907_;
}
v___jp_1908_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1911_);
v___y_1894_ = v___y_1909_;
v___y_1895_ = v___y_1910_;
v_a_1896_ = v___x_1912_;
goto v___jp_1893_;
}
v___jp_1913_:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1916_);
v___y_1894_ = v___y_1914_;
v___y_1895_ = v___y_1915_;
v_a_1896_ = v___x_1917_;
goto v___jp_1893_;
}
v___jp_1918_:
{
lean_object* v___x_1922_; double v___x_1923_; double v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1922_ = lean_io_get_num_heartbeats();
v___x_1923_ = lean_float_of_nat(v___y_1920_);
v___x_1924_ = lean_float_of_nat(v___x_1922_);
v___x_1925_ = lean_box_float(v___x_1923_);
v___x_1926_ = lean_box_float(v___x_1924_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1921_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1889_, v_hasTrace_1813_, v___x_1890_, v_options_1811_, v___x_1892_, v___y_1919_, v___f_1888_, v___x_1928_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
return v___x_1929_;
}
v___jp_1930_:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1933_);
v___y_1919_ = v___y_1931_;
v___y_1920_ = v___y_1932_;
v_a_1921_ = v___x_1934_;
goto v___jp_1918_;
}
v___jp_1935_:
{
lean_object* v___x_1939_; 
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1938_);
v___y_1919_ = v___y_1936_;
v___y_1920_ = v___y_1937_;
v_a_1921_ = v___x_1939_;
goto v___jp_1918_;
}
v___jp_1940_:
{
lean_object* v___x_1941_; lean_object* v_a_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1941_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1808_);
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1944_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1811_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1804_);
v___x_1946_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
if (lean_obj_tag(v_a_1947_) == 5)
{
lean_object* v_val_1948_; uint8_t v_isRec_1949_; 
v_val_1948_ = lean_ctor_get(v_a_1947_, 0);
lean_inc_ref(v_val_1948_);
lean_dec_ref_known(v_a_1947_, 1);
v_isRec_1949_ = lean_ctor_get_uint8(v_val_1948_, sizeof(void*)*6);
if (v_isRec_1949_ == 0)
{
lean_object* v___x_1950_; 
lean_dec_ref(v_val_1948_);
lean_dec(v_indName_1804_);
v___x_1950_ = lean_box(0);
v___y_1909_ = v___x_1945_;
v___y_1910_ = v_a_1942_;
v_a_1911_ = v___x_1950_;
goto v___jp_1908_;
}
else
{
lean_object* v_toConstantVal_1951_; lean_object* v_numParams_1952_; lean_object* v_all_1953_; lean_object* v_numNested_1954_; lean_object* v_type_1955_; lean_object* v___x_1956_; 
v_toConstantVal_1951_ = lean_ctor_get(v_val_1948_, 0);
lean_inc_ref(v_toConstantVal_1951_);
v_numParams_1952_ = lean_ctor_get(v_val_1948_, 1);
lean_inc(v_numParams_1952_);
v_all_1953_ = lean_ctor_get(v_val_1948_, 3);
lean_inc(v_all_1953_);
v_numNested_1954_ = lean_ctor_get(v_val_1948_, 5);
lean_inc(v_numNested_1954_);
lean_dec_ref(v_val_1948_);
v_type_1955_ = lean_ctor_get(v_toConstantVal_1951_, 2);
lean_inc_ref(v_type_1955_);
lean_dec_ref(v_toConstantVal_1951_);
v___x_1956_ = l_Lean_Meta_isPropFormerType(v_type_1955_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1958_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_inc_n(v_indName_1804_, 2);
v___x_1959_ = l_Lean_mkRecName(v_indName_1804_);
v___x_1960_ = l_Lean_mkBelowName(v_indName_1804_);
lean_inc(v___x_1960_);
lean_inc(v_numParams_1952_);
lean_inc(v___x_1959_);
v___x_1961_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1959_, v_numParams_1952_, v___x_1960_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
lean_dec_ref_known(v___x_1961_, 1);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = l_List_get_x21Internal___redArg(v___x_1814_, v_all_1953_, v___x_1962_);
lean_dec(v_all_1953_);
v___x_1964_ = lean_name_eq(v___x_1963_, v_indName_1804_);
lean_dec(v_indName_1804_);
lean_dec(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; 
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
lean_dec(v_numNested_1954_);
lean_dec(v_numParams_1952_);
v___x_1965_ = lean_box(0);
v___y_1909_ = v___x_1945_;
v___y_1910_ = v_a_1942_;
v_a_1911_ = v___x_1965_;
goto v___jp_1908_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_box(0);
v___x_1967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1954_, v___x_1959_, v___x_1960_, v_numParams_1952_, v___x_1962_, v___x_1966_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_numNested_1954_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec_ref_known(v___x_1967_, 1);
v___y_1909_ = v___x_1945_;
v___y_1910_ = v_a_1942_;
v_a_1911_ = v___x_1966_;
goto v___jp_1908_;
}
else
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___y_1914_ = v___x_1945_;
v___y_1915_ = v_a_1942_;
v_a_1916_ = v_a_1968_;
goto v___jp_1913_;
}
}
}
else
{
lean_object* v_a_1969_; 
lean_dec(v___x_1960_);
lean_dec(v___x_1959_);
lean_dec(v_numNested_1954_);
lean_dec(v_all_1953_);
lean_dec(v_numParams_1952_);
lean_dec(v_indName_1804_);
v_a_1969_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1961_, 1);
v___y_1914_ = v___x_1945_;
v___y_1915_ = v_a_1942_;
v_a_1916_ = v_a_1969_;
goto v___jp_1913_;
}
}
else
{
lean_object* v___x_1970_; 
lean_dec(v_numNested_1954_);
lean_dec(v_all_1953_);
lean_dec(v_numParams_1952_);
lean_dec(v_indName_1804_);
v___x_1970_ = lean_box(0);
v___y_1909_ = v___x_1945_;
v___y_1910_ = v_a_1942_;
v_a_1911_ = v___x_1970_;
goto v___jp_1908_;
}
}
else
{
lean_object* v_a_1971_; 
lean_dec(v_numNested_1954_);
lean_dec(v_all_1953_);
lean_dec(v_numParams_1952_);
lean_dec(v_indName_1804_);
v_a_1971_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1956_, 1);
v___y_1914_ = v___x_1945_;
v___y_1915_ = v_a_1942_;
v_a_1916_ = v_a_1971_;
goto v___jp_1913_;
}
}
}
else
{
lean_object* v___x_1972_; 
lean_dec(v_a_1947_);
lean_dec(v_indName_1804_);
v___x_1972_ = lean_box(0);
v___y_1909_ = v___x_1945_;
v___y_1910_ = v_a_1942_;
v_a_1911_ = v___x_1972_;
goto v___jp_1908_;
}
}
else
{
lean_object* v_a_1973_; 
lean_dec(v_indName_1804_);
v_a_1973_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1946_, 1);
v___y_1914_ = v___x_1945_;
v___y_1915_ = v_a_1942_;
v_a_1916_ = v_a_1973_;
goto v___jp_1913_;
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1804_);
v___x_1975_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1975_, 1);
if (lean_obj_tag(v_a_1976_) == 5)
{
lean_object* v_val_1977_; uint8_t v_isRec_1978_; 
v_val_1977_ = lean_ctor_get(v_a_1976_, 0);
lean_inc_ref(v_val_1977_);
lean_dec_ref_known(v_a_1976_, 1);
v_isRec_1978_ = lean_ctor_get_uint8(v_val_1977_, sizeof(void*)*6);
if (v_isRec_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v_val_1977_);
lean_dec(v_indName_1804_);
v___x_1979_ = lean_box(0);
v___y_1931_ = v_a_1942_;
v___y_1932_ = v___x_1974_;
v_a_1933_ = v___x_1979_;
goto v___jp_1930_;
}
else
{
lean_object* v_toConstantVal_1980_; lean_object* v_numParams_1981_; lean_object* v_all_1982_; lean_object* v_numNested_1983_; lean_object* v_type_1984_; lean_object* v___x_1985_; 
v_toConstantVal_1980_ = lean_ctor_get(v_val_1977_, 0);
lean_inc_ref(v_toConstantVal_1980_);
v_numParams_1981_ = lean_ctor_get(v_val_1977_, 1);
lean_inc(v_numParams_1981_);
v_all_1982_ = lean_ctor_get(v_val_1977_, 3);
lean_inc(v_all_1982_);
v_numNested_1983_ = lean_ctor_get(v_val_1977_, 5);
lean_inc(v_numNested_1983_);
lean_dec_ref(v_val_1977_);
v_type_1984_ = lean_ctor_get(v_toConstantVal_1980_, 2);
lean_inc_ref(v_type_1984_);
lean_dec_ref(v_toConstantVal_1980_);
v___x_1985_ = l_Lean_Meta_isPropFormerType(v_type_1984_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; uint8_t v___x_1987_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = lean_unbox(v_a_1986_);
lean_dec(v_a_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_inc_n(v_indName_1804_, 2);
v___x_1988_ = l_Lean_mkRecName(v_indName_1804_);
v___x_1989_ = l_Lean_mkBelowName(v_indName_1804_);
lean_inc(v___x_1989_);
lean_inc(v_numParams_1981_);
lean_inc(v___x_1988_);
v___x_1990_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1988_, v_numParams_1981_, v___x_1989_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
lean_dec_ref_known(v___x_1990_, 1);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = l_List_get_x21Internal___redArg(v___x_1814_, v_all_1982_, v___x_1991_);
lean_dec(v_all_1982_);
v___x_1993_ = lean_name_eq(v___x_1992_, v_indName_1804_);
lean_dec(v_indName_1804_);
lean_dec(v___x_1992_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_dec(v___x_1989_);
lean_dec(v___x_1988_);
lean_dec(v_numNested_1983_);
lean_dec(v_numParams_1981_);
v___x_1994_ = lean_box(0);
v___y_1931_ = v_a_1942_;
v___y_1932_ = v___x_1974_;
v_a_1933_ = v___x_1994_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_box(0);
v___x_1996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1983_, v___x_1988_, v___x_1989_, v_numParams_1981_, v___x_1991_, v___x_1995_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_numNested_1983_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref_known(v___x_1996_, 1);
v___y_1931_ = v_a_1942_;
v___y_1932_ = v___x_1974_;
v_a_1933_ = v___x_1995_;
goto v___jp_1930_;
}
else
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1936_ = v_a_1942_;
v___y_1937_ = v___x_1974_;
v_a_1938_ = v_a_1997_;
goto v___jp_1935_;
}
}
}
else
{
lean_object* v_a_1998_; 
lean_dec(v___x_1989_);
lean_dec(v___x_1988_);
lean_dec(v_numNested_1983_);
lean_dec(v_all_1982_);
lean_dec(v_numParams_1981_);
lean_dec(v_indName_1804_);
v_a_1998_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1936_ = v_a_1942_;
v___y_1937_ = v___x_1974_;
v_a_1938_ = v_a_1998_;
goto v___jp_1935_;
}
}
else
{
lean_object* v___x_1999_; 
lean_dec(v_numNested_1983_);
lean_dec(v_all_1982_);
lean_dec(v_numParams_1981_);
lean_dec(v_indName_1804_);
v___x_1999_ = lean_box(0);
v___y_1931_ = v_a_1942_;
v___y_1932_ = v___x_1974_;
v_a_1933_ = v___x_1999_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_2000_; 
lean_dec(v_numNested_1983_);
lean_dec(v_all_1982_);
lean_dec(v_numParams_1981_);
lean_dec(v_indName_1804_);
v_a_2000_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1985_, 1);
v___y_1936_ = v_a_1942_;
v___y_1937_ = v___x_1974_;
v_a_1938_ = v_a_2000_;
goto v___jp_1935_;
}
}
}
else
{
lean_object* v___x_2001_; 
lean_dec(v_a_1976_);
lean_dec(v_indName_1804_);
v___x_2001_ = lean_box(0);
v___y_1931_ = v_a_1942_;
v___y_1932_ = v___x_1974_;
v_a_1933_ = v___x_2001_;
goto v___jp_1930_;
}
}
else
{
lean_object* v_a_2002_; 
lean_dec(v_indName_1804_);
v_a_2002_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_1975_, 1);
v___y_1936_ = v_a_1942_;
v___y_1937_ = v___x_1974_;
v_a_1938_ = v_a_2002_;
goto v___jp_1935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_mkBelow(v_indName_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2085_, lean_object* v___x_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v_inst_2089_, lean_object* v_R_2090_, lean_object* v_a_2091_, lean_object* v_b_2092_, lean_object* v_c_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2085_, v___x_2086_, v___x_2087_, v___x_2088_, v_a_2091_, v_b_2092_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2100_, lean_object* v___x_2101_, lean_object* v___x_2102_, lean_object* v___x_2103_, lean_object* v_inst_2104_, lean_object* v_R_2105_, lean_object* v_a_2106_, lean_object* v_b_2107_, lean_object* v_c_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2100_, v___x_2101_, v___x_2102_, v___x_2103_, v_inst_2104_, v_R_2105_, v_a_2106_, v_b_2107_, v_c_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v_upperBound_2100_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2116_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2123_, lean_object* v_x_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2123_, v_x_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
if (lean_obj_tag(v_a_2131_) == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = l_List_reverse___redArg(v_a_2132_);
return v___x_2133_;
}
else
{
lean_object* v_head_2134_; lean_object* v_tail_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2144_; 
v_head_2134_ = lean_ctor_get(v_a_2131_, 0);
v_tail_2135_ = lean_ctor_get(v_a_2131_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_a_2131_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2137_ = v_a_2131_;
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_tail_2135_);
lean_inc(v_head_2134_);
lean_dec(v_a_2131_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2144_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = l_Lean_MessageData_ofExpr(v_head_2134_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 1, v_a_2132_);
lean_ctor_set(v___x_2137_, 0, v___x_2139_);
v___x_2141_ = v___x_2137_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_a_2132_);
v___x_2141_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v_a_2131_ = v_tail_2135_;
v_a_2132_ = v___x_2141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2145_, lean_object* v_v_2146_, lean_object* v_i_2147_){
_start:
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = lean_array_get_size(v_xs_2145_);
v___x_2149_ = lean_nat_dec_lt(v_i_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_i_2147_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = lean_array_fget_borrowed(v_xs_2145_, v_i_2147_);
v___x_2152_ = lean_expr_eqv(v___x_2151_, v_v_2146_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_unsigned_to_nat(1u);
v___x_2154_ = lean_nat_add(v_i_2147_, v___x_2153_);
lean_dec(v_i_2147_);
v_i_2147_ = v___x_2154_;
goto _start;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2156_, 0, v_i_2147_);
return v___x_2156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2157_, lean_object* v_v_2158_, lean_object* v_i_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2157_, v_v_2158_, v_i_2159_);
lean_dec_ref(v_v_2158_);
lean_dec_ref(v_xs_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2161_, lean_object* v_v_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2161_, v_v_2162_, v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2165_, lean_object* v_v_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2165_, v_v_2166_);
lean_dec_ref(v_v_2166_);
lean_dec_ref(v_xs_2165_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2168_, lean_object* v_v_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2168_, v_v_2169_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v_val_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_val_2172_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2170_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_val_2172_);
lean_dec(v___x_2170_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_val_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2180_, lean_object* v_v_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2180_, v_v_2181_);
lean_dec_ref(v_v_2181_);
lean_dec_ref(v_xs_2180_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2189_, lean_object* v_prods_2190_, lean_object* v_motives_2191_, lean_object* v_fs_2192_, lean_object* v_minor__type_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
if (lean_obj_tag(v_x_2194_) == 5)
{
lean_object* v_fn_2202_; lean_object* v_arg_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v_fn_2202_ = lean_ctor_get(v_x_2194_, 0);
lean_inc_ref(v_fn_2202_);
v_arg_2203_ = lean_ctor_get(v_x_2194_, 1);
lean_inc_ref(v_arg_2203_);
lean_dec_ref_known(v_x_2194_, 2);
v___x_2204_ = lean_array_set(v_x_2195_, v_x_2196_, v_arg_2203_);
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_sub(v_x_2196_, v___x_2205_);
lean_dec(v_x_2196_);
v_x_2194_ = v_fn_2202_;
v_x_2195_ = v___x_2204_;
v_x_2196_ = v___x_2206_;
goto _start;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_x_2196_);
v___x_2208_ = l_Lean_instInhabitedExpr;
v___x_2209_ = l_Lean_Meta_PProdN_mk(v_rlvl_2189_, v_prods_2190_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2191_, v_x_2194_);
lean_dec_ref(v_x_2194_);
if (lean_obj_tag(v___x_2211_) == 1)
{
lean_object* v_val_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v_minor__type_2193_);
lean_dec_ref(v_motives_2191_);
v_val_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_val_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = lean_array_get_borrowed(v___x_2208_, v_fs_2192_, v_val_2212_);
lean_dec(v_val_2212_);
lean_inc(v_a_2210_);
v___x_2214_ = lean_array_push(v_x_2195_, v_a_2210_);
lean_inc(v___x_2213_);
v___x_2215_ = l_Lean_mkAppN(v___x_2213_, v___x_2214_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = l_Lean_Meta_mkPProdMk(v___x_2215_, v_a_2210_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
return v___x_2216_;
}
else
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec(v___x_2211_);
lean_dec(v_a_2210_);
lean_dec_ref(v_x_2195_);
v___x_2217_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2218_ = l_Lean_MessageData_ofExpr(v_minor__type_2193_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = lean_array_to_list(v_motives_2191_);
v___x_2223_ = lean_box(0);
v___x_2224_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2222_, v___x_2223_);
v___x_2225_ = l_Lean_MessageData_ofList(v___x_2224_);
v___x_2226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2221_);
lean_ctor_set(v___x_2226_, 1, v___x_2225_);
v___x_2227_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2226_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
return v___x_2227_;
}
}
else
{
lean_dec_ref(v_x_2195_);
lean_dec_ref(v_x_2194_);
lean_dec_ref(v_minor__type_2193_);
lean_dec_ref(v_motives_2191_);
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2228_, lean_object* v_prods_2229_, lean_object* v_motives_2230_, lean_object* v_fs_2231_, lean_object* v_minor__type_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2228_, v_prods_2229_, v_motives_2230_, v_fs_2231_, v_minor__type_2232_, v_x_2233_, v_x_2234_, v_x_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_fs_2231_);
return v_res_2241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2242_; lean_object* v_dummy_2243_; 
v___x_2242_ = lean_box(0);
v_dummy_2243_ = l_Lean_Expr_sort___override(v___x_2242_);
return v_dummy_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2244_, lean_object* v_head_2245_, lean_object* v_belows_2246_, lean_object* v_prods_2247_, lean_object* v_rlvl_2248_, lean_object* v_fs_2249_, lean_object* v_minor__type_2250_, lean_object* v_tail_2251_, lean_object* v_arg__args_2252_, lean_object* v_arg__type_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2244_, v_head_2245_, v_belows_2246_, v_prods_2247_, v_rlvl_2248_, v_fs_2249_, v_minor__type_2250_, v_tail_2251_, v_arg__args_2252_, v_arg__type_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_arg__args_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2260_, lean_object* v_motives_2261_, lean_object* v_belows_2262_, lean_object* v_fs_2263_, lean_object* v_minor__type_2264_, lean_object* v_prods_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
if (lean_obj_tag(v_a_2266_) == 0)
{
lean_object* v_dummy_2272_; lean_object* v_nargs_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v_belows_2262_);
v_dummy_2272_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2273_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2264_);
lean_inc(v_nargs_2273_);
v___x_2274_ = lean_mk_array(v_nargs_2273_, v_dummy_2272_);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = lean_nat_sub(v_nargs_2273_, v___x_2275_);
lean_dec(v_nargs_2273_);
lean_inc_ref(v_minor__type_2264_);
v___x_2277_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2260_, v_prods_2265_, v_motives_2261_, v_fs_2263_, v_minor__type_2264_, v_minor__type_2264_, v___x_2274_, v___x_2276_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
lean_dec_ref(v_fs_2263_);
return v___x_2277_;
}
else
{
lean_object* v_head_2278_; lean_object* v_tail_2279_; lean_object* v___f_2280_; lean_object* v___x_2281_; 
v_head_2278_ = lean_ctor_get(v_a_2266_, 0);
lean_inc_n(v_head_2278_, 2);
v_tail_2279_ = lean_ctor_get(v_a_2266_, 1);
lean_inc(v_tail_2279_);
lean_dec_ref_known(v_a_2266_, 2);
v___f_2280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2280_, 0, v_motives_2261_);
lean_closure_set(v___f_2280_, 1, v_head_2278_);
lean_closure_set(v___f_2280_, 2, v_belows_2262_);
lean_closure_set(v___f_2280_, 3, v_prods_2265_);
lean_closure_set(v___f_2280_, 4, v_rlvl_2260_);
lean_closure_set(v___f_2280_, 5, v_fs_2263_);
lean_closure_set(v___f_2280_, 6, v_minor__type_2264_);
lean_closure_set(v___f_2280_, 7, v_tail_2279_);
lean_inc(v_a_2270_);
lean_inc_ref(v_a_2269_);
lean_inc(v_a_2268_);
lean_inc_ref(v_a_2267_);
v___x_2281_ = lean_infer_type(v_head_2278_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; uint8_t v___x_2283_; lean_object* v___x_2284_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = 0;
v___x_2284_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2282_, v___f_2280_, v___x_2283_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
return v___x_2284_;
}
else
{
lean_dec_ref(v___f_2280_);
return v___x_2281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2285_, lean_object* v_rlvl_2286_, lean_object* v_motives_2287_, lean_object* v_belows_2288_, lean_object* v_fs_2289_, lean_object* v_minor__type_2290_, lean_object* v_tail_2291_, uint8_t v___x_2292_, uint8_t v___x_2293_, uint8_t v___x_2294_, lean_object* v_arg_x27_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_inc_ref(v_arg_x27_2295_);
v___x_2301_ = lean_array_push(v_prods_2285_, v_arg_x27_2295_);
v___x_2302_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2286_, v_motives_2287_, v_belows_2288_, v_fs_2289_, v_minor__type_2290_, v___x_2301_, v_tail_2291_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
v___x_2306_ = lean_array_push(v___x_2305_, v_arg_x27_2295_);
v___x_2307_ = l_Lean_Meta_mkLambdaFVars(v___x_2306_, v_a_2303_, v___x_2292_, v___x_2293_, v___x_2292_, v___x_2293_, v___x_2294_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v___x_2306_);
return v___x_2307_;
}
else
{
lean_dec_ref(v_arg_x27_2295_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2308_, lean_object* v_rlvl_2309_, lean_object* v_motives_2310_, lean_object* v_belows_2311_, lean_object* v_fs_2312_, lean_object* v_minor__type_2313_, lean_object* v_tail_2314_, lean_object* v___x_2315_, lean_object* v___x_2316_, lean_object* v___x_2317_, lean_object* v_arg_x27_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
uint8_t v___x_1689__boxed_2324_; uint8_t v___x_1690__boxed_2325_; uint8_t v___x_1691__boxed_2326_; lean_object* v_res_2327_; 
v___x_1689__boxed_2324_ = lean_unbox(v___x_2315_);
v___x_1690__boxed_2325_ = lean_unbox(v___x_2316_);
v___x_1691__boxed_2326_ = lean_unbox(v___x_2317_);
v_res_2327_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2308_, v_rlvl_2309_, v_motives_2310_, v_belows_2311_, v_fs_2312_, v_minor__type_2313_, v_tail_2314_, v___x_1689__boxed_2324_, v___x_1690__boxed_2325_, v___x_1691__boxed_2326_, v_arg_x27_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2328_, lean_object* v_head_2329_, lean_object* v_belows_2330_, lean_object* v_arg__type_2331_, lean_object* v_prods_2332_, lean_object* v_rlvl_2333_, lean_object* v_fs_2334_, lean_object* v_minor__type_2335_, lean_object* v_tail_2336_, lean_object* v_arg__args_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
if (lean_obj_tag(v_x_2338_) == 5)
{
lean_object* v_fn_2346_; lean_object* v_arg_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_fn_2346_ = lean_ctor_get(v_x_2338_, 0);
lean_inc_ref(v_fn_2346_);
v_arg_2347_ = lean_ctor_get(v_x_2338_, 1);
lean_inc_ref(v_arg_2347_);
lean_dec_ref_known(v_x_2338_, 2);
v___x_2348_ = lean_array_set(v_x_2339_, v_x_2340_, v_arg_2347_);
v___x_2349_ = lean_unsigned_to_nat(1u);
v___x_2350_ = lean_nat_sub(v_x_2340_, v___x_2349_);
lean_dec(v_x_2340_);
v_x_2338_ = v_fn_2346_;
v_x_2339_ = v___x_2348_;
v_x_2340_ = v___x_2350_;
goto _start;
}
else
{
lean_object* v___x_2352_; 
lean_dec(v_x_2340_);
v___x_2352_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2328_, v_x_2338_);
lean_dec_ref(v_x_2338_);
if (lean_obj_tag(v___x_2352_) == 1)
{
lean_object* v_val_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_val_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_val_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = l_Lean_instInhabitedExpr;
v___x_2355_ = l_Lean_Expr_fvarId_x21(v_head_2329_);
lean_dec_ref(v_head_2329_);
v___x_2356_ = l_Lean_FVarId_getUserName___redArg(v___x_2355_, v___y_2341_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v___x_2356_, 1);
v___x_2358_ = lean_array_get_borrowed(v___x_2354_, v_belows_2330_, v_val_2353_);
lean_dec(v_val_2353_);
lean_inc(v___x_2358_);
v___x_2359_ = l_Lean_mkAppN(v___x_2358_, v_x_2339_);
lean_dec_ref(v_x_2339_);
v___x_2360_ = l_Lean_Meta_mkPProd(v_arg__type_2331_, v___x_2359_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; uint8_t v___x_2362_; uint8_t v___x_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___f_2368_; lean_object* v___x_2369_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = 0;
v___x_2363_ = 1;
v___x_2364_ = 1;
v___x_2365_ = lean_box(v___x_2362_);
v___x_2366_ = lean_box(v___x_2363_);
v___x_2367_ = lean_box(v___x_2364_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2368_, 0, v_prods_2332_);
lean_closure_set(v___f_2368_, 1, v_rlvl_2333_);
lean_closure_set(v___f_2368_, 2, v_motives_2328_);
lean_closure_set(v___f_2368_, 3, v_belows_2330_);
lean_closure_set(v___f_2368_, 4, v_fs_2334_);
lean_closure_set(v___f_2368_, 5, v_minor__type_2335_);
lean_closure_set(v___f_2368_, 6, v_tail_2336_);
lean_closure_set(v___f_2368_, 7, v___x_2365_);
lean_closure_set(v___f_2368_, 8, v___x_2366_);
lean_closure_set(v___f_2368_, 9, v___x_2367_);
v___x_2369_ = l_Lean_Meta_mkForallFVars(v_arg__args_2337_, v_a_2361_, v___x_2362_, v___x_2363_, v___x_2363_, v___x_2364_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2357_, v_a_2370_, v___f_2368_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2371_;
}
else
{
lean_dec_ref(v___f_2368_);
lean_dec(v_a_2357_);
return v___x_2369_;
}
}
else
{
lean_dec(v_a_2357_);
lean_dec(v_tail_2336_);
lean_dec_ref(v_minor__type_2335_);
lean_dec_ref(v_fs_2334_);
lean_dec(v_rlvl_2333_);
lean_dec_ref(v_prods_2332_);
lean_dec_ref(v_belows_2330_);
lean_dec_ref(v_motives_2328_);
return v___x_2360_;
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_val_2353_);
lean_dec_ref(v_x_2339_);
lean_dec(v_tail_2336_);
lean_dec_ref(v_minor__type_2335_);
lean_dec_ref(v_fs_2334_);
lean_dec(v_rlvl_2333_);
lean_dec_ref(v_prods_2332_);
lean_dec_ref(v_arg__type_2331_);
lean_dec_ref(v_belows_2330_);
lean_dec_ref(v_motives_2328_);
v_a_2372_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2356_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2356_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v___x_2380_; 
lean_dec(v___x_2352_);
lean_dec_ref(v_x_2339_);
lean_dec_ref(v_arg__type_2331_);
v___x_2380_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2333_, v_motives_2328_, v_belows_2330_, v_fs_2334_, v_minor__type_2335_, v_prods_2332_, v_tail_2336_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = lean_unsigned_to_nat(1u);
v___x_2383_ = lean_mk_empty_array_with_capacity(v___x_2382_);
v___x_2384_ = lean_array_push(v___x_2383_, v_head_2329_);
v___x_2385_ = 0;
v___x_2386_ = 1;
v___x_2387_ = 1;
v___x_2388_ = l_Lean_Meta_mkLambdaFVars(v___x_2384_, v_a_2381_, v___x_2385_, v___x_2386_, v___x_2385_, v___x_2386_, v___x_2387_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec_ref(v___x_2384_);
return v___x_2388_;
}
else
{
lean_dec_ref(v_head_2329_);
return v___x_2380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2389_, lean_object* v_head_2390_, lean_object* v_belows_2391_, lean_object* v_prods_2392_, lean_object* v_rlvl_2393_, lean_object* v_fs_2394_, lean_object* v_minor__type_2395_, lean_object* v_tail_2396_, lean_object* v_arg__args_2397_, lean_object* v_arg__type_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_dummy_2404_; lean_object* v_nargs_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_dummy_2404_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2405_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2398_);
lean_inc(v_nargs_2405_);
v___x_2406_ = lean_mk_array(v_nargs_2405_, v_dummy_2404_);
v___x_2407_ = lean_unsigned_to_nat(1u);
v___x_2408_ = lean_nat_sub(v_nargs_2405_, v___x_2407_);
lean_dec(v_nargs_2405_);
lean_inc_ref(v_arg__type_2398_);
v___x_2409_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2389_, v_head_2390_, v_belows_2391_, v_arg__type_2398_, v_prods_2392_, v_rlvl_2393_, v_fs_2394_, v_minor__type_2395_, v_tail_2396_, v_arg__args_2397_, v_arg__type_2398_, v___x_2406_, v___x_2408_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2410_, lean_object* v_motives_2411_, lean_object* v_belows_2412_, lean_object* v_fs_2413_, lean_object* v_minor__type_2414_, lean_object* v_prods_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2410_, v_motives_2411_, v_belows_2412_, v_fs_2413_, v_minor__type_2414_, v_prods_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2423_ = _args[0];
lean_object* v_head_2424_ = _args[1];
lean_object* v_belows_2425_ = _args[2];
lean_object* v_arg__type_2426_ = _args[3];
lean_object* v_prods_2427_ = _args[4];
lean_object* v_rlvl_2428_ = _args[5];
lean_object* v_fs_2429_ = _args[6];
lean_object* v_minor__type_2430_ = _args[7];
lean_object* v_tail_2431_ = _args[8];
lean_object* v_arg__args_2432_ = _args[9];
lean_object* v_x_2433_ = _args[10];
lean_object* v_x_2434_ = _args[11];
lean_object* v_x_2435_ = _args[12];
lean_object* v___y_2436_ = _args[13];
lean_object* v___y_2437_ = _args[14];
lean_object* v___y_2438_ = _args[15];
lean_object* v___y_2439_ = _args[16];
lean_object* v___y_2440_ = _args[17];
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2423_, v_head_2424_, v_belows_2425_, v_arg__type_2426_, v_prods_2427_, v_rlvl_2428_, v_fs_2429_, v_minor__type_2430_, v_tail_2431_, v_arg__args_2432_, v_x_2433_, v_x_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_arg__args_2432_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2442_, lean_object* v_motives_2443_, lean_object* v_belows_2444_, lean_object* v_fs_2445_, lean_object* v_minor__args_2446_, lean_object* v_minor__type_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2454_ = lean_array_to_list(v_minor__args_2446_);
v___x_2455_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2442_, v_motives_2443_, v_belows_2444_, v_fs_2445_, v_minor__type_2447_, v___x_2453_, v___x_2454_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2456_, lean_object* v_motives_2457_, lean_object* v_belows_2458_, lean_object* v_fs_2459_, lean_object* v_minor__args_2460_, lean_object* v_minor__type_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2456_, v_motives_2457_, v_belows_2458_, v_fs_2459_, v_minor__args_2460_, v_minor__type_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2468_, lean_object* v_motives_2469_, lean_object* v_belows_2470_, lean_object* v_fs_2471_, lean_object* v_minorType_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___f_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; 
v___f_2478_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2478_, 0, v_rlvl_2468_);
lean_closure_set(v___f_2478_, 1, v_motives_2469_);
lean_closure_set(v___f_2478_, 2, v_belows_2470_);
lean_closure_set(v___f_2478_, 3, v_fs_2471_);
v___x_2479_ = 0;
v___x_2480_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2472_, v___f_2478_, v___x_2479_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2481_, lean_object* v_motives_2482_, lean_object* v_belows_2483_, lean_object* v_fs_2484_, lean_object* v_minorType_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2481_, v_motives_2482_, v_belows_2483_, v_fs_2484_, v_minorType_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___f_2498_; lean_object* v___x_27356__overap_2499_; lean_object* v___x_2500_; 
v___f_2498_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27356__overap_2499_ = lean_panic_fn_borrowed(v___f_2498_, v_msg_2492_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v___x_2500_ = lean_apply_5(v___x_27356__overap_2499_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_Expr_hasMVar(v_e_2508_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v_e_2508_);
return v___x_2512_;
}
else
{
lean_object* v___x_2513_; lean_object* v_mctx_2514_; lean_object* v___x_2515_; lean_object* v_fst_2516_; lean_object* v_snd_2517_; lean_object* v___x_2518_; lean_object* v_cache_2519_; lean_object* v_zetaDeltaFVarIds_2520_; lean_object* v_postponed_2521_; lean_object* v_diag_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2531_; 
v___x_2513_ = lean_st_ref_get(v___y_2509_);
v_mctx_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc_ref(v_mctx_2514_);
lean_dec(v___x_2513_);
v___x_2515_ = l_Lean_instantiateMVarsCore(v_mctx_2514_, v_e_2508_);
v_fst_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_fst_2516_);
v_snd_2517_ = lean_ctor_get(v___x_2515_, 1);
lean_inc(v_snd_2517_);
lean_dec_ref(v___x_2515_);
v___x_2518_ = lean_st_ref_take(v___y_2509_);
v_cache_2519_ = lean_ctor_get(v___x_2518_, 1);
v_zetaDeltaFVarIds_2520_ = lean_ctor_get(v___x_2518_, 2);
v_postponed_2521_ = lean_ctor_get(v___x_2518_, 3);
v_diag_2522_ = lean_ctor_get(v___x_2518_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2518_, 0);
lean_dec(v_unused_2532_);
v___x_2524_ = v___x_2518_;
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_diag_2522_);
lean_inc(v_postponed_2521_);
lean_inc(v_zetaDeltaFVarIds_2520_);
lean_inc(v_cache_2519_);
lean_dec(v___x_2518_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2531_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v_snd_2517_);
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_snd_2517_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_cache_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_zetaDeltaFVarIds_2520_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_postponed_2521_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_diag_2522_);
v___x_2527_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_st_ref_put(v___y_2509_, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_fst_2516_);
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2533_, v___y_2534_);
lean_dec(v___y_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2537_, v___y_2539_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v_env_2555_; lean_object* v_toConstantVal_2556_; lean_object* v_value_2557_; lean_object* v_all_2558_; lean_object* v_type_2565_; uint8_t v___x_2566_; 
v___x_2554_ = lean_st_ref_get(v___y_2552_);
v_env_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc_ref_n(v_env_2555_, 2);
lean_dec(v___x_2554_);
v_toConstantVal_2556_ = lean_ctor_get(v_thm_2551_, 0);
v_value_2557_ = lean_ctor_get(v_thm_2551_, 1);
v_all_2558_ = lean_ctor_get(v_thm_2551_, 2);
v_type_2565_ = lean_ctor_get(v_toConstantVal_2556_, 2);
v___x_2566_ = l_Lean_Environment_hasUnsafe(v_env_2555_, v_type_2565_);
if (v___x_2566_ == 0)
{
uint8_t v___x_2567_; 
v___x_2567_ = l_Lean_Environment_hasUnsafe(v_env_2555_, v_value_2557_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_thm_2551_);
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2568_);
return v___x_2569_;
}
else
{
lean_inc(v_all_2558_);
lean_inc_ref(v_value_2557_);
lean_inc_ref(v_toConstantVal_2556_);
lean_dec_ref(v_thm_2551_);
goto v___jp_2559_;
}
}
else
{
lean_inc(v_all_2558_);
lean_inc_ref(v_value_2557_);
lean_inc_ref(v_toConstantVal_2556_);
lean_dec_ref(v_env_2555_);
lean_dec_ref(v_thm_2551_);
goto v___jp_2559_;
}
v___jp_2559_:
{
lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2560_ = lean_box(0);
v___x_2561_ = 0;
v___x_2562_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2562_, 0, v_toConstantVal_2556_);
lean_ctor_set(v___x_2562_, 1, v_value_2557_);
lean_ctor_set(v___x_2562_, 2, v___x_2560_);
lean_ctor_set(v___x_2562_, 3, v_all_2558_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*4, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2570_, v___y_2571_);
lean_dec(v___y_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2574_, v___y_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2589_, lean_object* v___x_2590_, lean_object* v___x_2591_, lean_object* v_all_2592_, lean_object* v___x_2593_, lean_object* v___x_2594_, lean_object* v___x_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v___y_2598_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2602_ = lean_array_get_size(v_all_2592_);
v___x_2603_ = lean_nat_dec_lt(v_x_2596_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2604_ = lean_array_get_borrowed(v___x_2593_, v_all_2592_, v___x_2594_);
v___x_2605_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2606_ = lean_nat_sub(v_x_2596_, v___x_2602_);
v___x_2607_ = lean_nat_add(v___x_2606_, v___x_2595_);
lean_dec(v___x_2606_);
v___x_2608_ = l_Nat_reprFast(v___x_2607_);
v___x_2609_ = lean_string_append(v___x_2605_, v___x_2608_);
lean_dec_ref(v___x_2608_);
lean_inc(v___x_2604_);
v___x_2610_ = l_Lean_Name_str___override(v___x_2604_, v___x_2609_);
v___y_2598_ = v___x_2610_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_array_fget_borrowed(v_all_2592_, v_x_2596_);
lean_inc(v___x_2611_);
v___x_2612_ = l_Lean_mkBelowName(v___x_2611_);
v___y_2598_ = v___x_2612_;
goto v___jp_2597_;
}
v___jp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = l_Lean_Expr_const___override(v___y_2598_, v___x_2589_);
v___x_2600_ = l_Array_append___redArg(v___x_2590_, v___x_2591_);
v___x_2601_ = l_Lean_mkAppN(v___x_2599_, v___x_2600_);
lean_dec_ref(v___x_2600_);
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v_all_2616_, lean_object* v___x_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2613_, v___x_2614_, v___x_2615_, v_all_2616_, v___x_2617_, v___x_2618_, v___x_2619_, v_x_2620_);
lean_dec(v_x_2620_);
lean_dec(v___x_2619_);
lean_dec(v___x_2618_);
lean_dec(v___x_2617_);
lean_dec_ref(v_all_2616_);
lean_dec_ref(v___x_2615_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2622_, lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v_fs_2625_, lean_object* v_as_2626_, size_t v_sz_2627_, size_t v_i_2628_, lean_object* v_b_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_usize_dec_lt(v_i_2628_, v_sz_2627_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref(v_fs_2625_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___x_2623_);
lean_dec(v___x_2622_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_b_2629_);
return v___x_2636_;
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2638_; 
v_a_2637_ = lean_array_uget_borrowed(v_as_2626_, v_i_2628_);
lean_inc(v___y_2633_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
lean_inc_ref(v___y_2630_);
lean_inc(v_a_2637_);
v___x_2638_ = lean_infer_type(v_a_2637_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
lean_inc_ref(v_fs_2625_);
lean_inc_ref(v___x_2624_);
lean_inc_ref(v___x_2623_);
lean_inc(v___x_2622_);
v___x_2640_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2622_, v___x_2623_, v___x_2624_, v_fs_2625_, v_a_2639_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; size_t v___x_2643_; size_t v___x_2644_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = l_Lean_Expr_app___override(v_b_2629_, v_a_2641_);
v___x_2643_ = ((size_t)1ULL);
v___x_2644_ = lean_usize_add(v_i_2628_, v___x_2643_);
v_i_2628_ = v___x_2644_;
v_b_2629_ = v___x_2642_;
goto _start;
}
else
{
lean_dec_ref(v_b_2629_);
lean_dec_ref(v_fs_2625_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___x_2623_);
lean_dec(v___x_2622_);
return v___x_2640_;
}
}
else
{
lean_dec_ref(v_b_2629_);
lean_dec_ref(v_fs_2625_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___x_2623_);
lean_dec(v___x_2622_);
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v_fs_2649_, lean_object* v_as_2650_, lean_object* v_sz_2651_, lean_object* v_i_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
size_t v_sz_boxed_2659_; size_t v_i_boxed_2660_; lean_object* v_res_2661_; 
v_sz_boxed_2659_ = lean_unbox_usize(v_sz_2651_);
lean_dec(v_sz_2651_);
v_i_boxed_2660_ = lean_unbox_usize(v_i_2652_);
lean_dec(v_i_2652_);
v_res_2661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2646_, v___x_2647_, v___x_2648_, v_fs_2649_, v_as_2650_, v_sz_boxed_2659_, v_i_boxed_2660_, v_b_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec_ref(v_as_2650_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2662_, lean_object* v___x_2663_, uint8_t v___x_2664_, lean_object* v_targs_2665_, lean_object* v_x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = l_Lean_mkAppN(v_a_2662_, v_targs_2665_);
v___x_2673_ = l_Lean_mkAppN(v___x_2663_, v_targs_2665_);
v___x_2674_ = l_Lean_Meta_mkPProd(v___x_2672_, v___x_2673_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = 0;
v___x_2677_ = 1;
v___x_2678_ = l_Lean_Meta_mkLambdaFVars(v_targs_2665_, v_a_2675_, v___x_2676_, v___x_2664_, v___x_2676_, v___x_2664_, v___x_2677_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2678_;
}
else
{
return v___x_2674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2679_, lean_object* v___x_2680_, lean_object* v___x_2681_, lean_object* v_targs_2682_, lean_object* v_x_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v___x_30622__boxed_2689_; lean_object* v_res_2690_; 
v___x_30622__boxed_2689_ = lean_unbox(v___x_2681_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2679_, v___x_2680_, v___x_30622__boxed_2689_, v_targs_2682_, v_x_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec_ref(v_x_2683_);
lean_dec_ref(v_targs_2682_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2691_, lean_object* v___x_2692_, lean_object* v_as_2693_, size_t v_sz_2694_, size_t v_i_2695_, lean_object* v_b_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_2702_; 
v___x_2702_ = lean_usize_dec_lt(v_i_2695_, v_sz_2694_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_b_2696_);
return v___x_2703_;
}
else
{
lean_object* v_snd_2704_; lean_object* v_fst_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2762_; 
v_snd_2704_ = lean_ctor_get(v_b_2696_, 1);
v_fst_2705_ = lean_ctor_get(v_b_2696_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_b_2696_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2707_ = v_b_2696_;
v_isShared_2708_ = v_isSharedCheck_2762_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_snd_2704_);
lean_inc(v_fst_2705_);
lean_dec(v_b_2696_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2762_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_array_2709_; lean_object* v_start_2710_; lean_object* v_stop_2711_; uint8_t v___x_2712_; 
v_array_2709_ = lean_ctor_get(v_snd_2704_, 0);
v_start_2710_ = lean_ctor_get(v_snd_2704_, 1);
v_stop_2711_ = lean_ctor_get(v_snd_2704_, 2);
v___x_2712_ = lean_nat_dec_lt(v_start_2710_, v_stop_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2714_; 
if (v_isShared_2708_ == 0)
{
v___x_2714_ = v___x_2707_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_fst_2705_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v_snd_2704_);
v___x_2714_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
return v___x_2715_;
}
}
else
{
lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2758_; 
lean_inc(v_stop_2711_);
lean_inc(v_start_2710_);
lean_inc_ref(v_array_2709_);
v_isSharedCheck_2758_ = !lean_is_exclusive(v_snd_2704_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; lean_object* v_unused_2760_; lean_object* v_unused_2761_; 
v_unused_2759_ = lean_ctor_get(v_snd_2704_, 2);
lean_dec(v_unused_2759_);
v_unused_2760_ = lean_ctor_get(v_snd_2704_, 1);
lean_dec(v_unused_2760_);
v_unused_2761_ = lean_ctor_get(v_snd_2704_, 0);
lean_dec(v_unused_2761_);
v___x_2718_ = v_snd_2704_;
v_isShared_2719_ = v_isSharedCheck_2758_;
goto v_resetjp_2717_;
}
else
{
lean_dec(v_snd_2704_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2758_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint8_t v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2720_ = lean_nat_dec_lt(v___x_2691_, v___x_2692_);
v_a_2721_ = lean_array_uget_borrowed(v_as_2693_, v_i_2695_);
v___x_2722_ = lean_array_fget_borrowed(v_array_2709_, v_start_2710_);
v___x_2723_ = lean_box(v___x_2720_);
lean_inc(v___x_2722_);
lean_inc(v_a_2721_);
v___f_2724_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2724_, 0, v_a_2721_);
lean_closure_set(v___f_2724_, 1, v___x_2722_);
lean_closure_set(v___f_2724_, 2, v___x_2723_);
v___x_2725_ = lean_unsigned_to_nat(1u);
v___x_2726_ = lean_nat_add(v_start_2710_, v___x_2725_);
lean_dec(v_start_2710_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2726_);
v___x_2728_ = v___x_2718_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_array_2709_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_stop_2711_);
v___x_2728_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2729_; 
lean_inc(v___y_2700_);
lean_inc_ref(v___y_2699_);
lean_inc(v___y_2698_);
lean_inc_ref(v___y_2697_);
lean_inc(v_a_2721_);
v___x_2729_ = lean_infer_type(v_a_2721_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = 0;
v___x_2732_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2730_, v___f_2724_, v___x_2731_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2736_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = l_Lean_Expr_app___override(v_fst_2705_, v_a_2733_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v___x_2728_);
lean_ctor_set(v___x_2707_, 0, v___x_2734_);
v___x_2736_ = v___x_2707_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2728_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
size_t v___x_2737_; size_t v___x_2738_; 
v___x_2737_ = ((size_t)1ULL);
v___x_2738_ = lean_usize_add(v_i_2695_, v___x_2737_);
v_i_2695_ = v___x_2738_;
v_b_2696_ = v___x_2736_;
goto _start;
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v___x_2728_);
lean_del_object(v___x_2707_);
lean_dec(v_fst_2705_);
v_a_2741_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2732_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2732_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v___x_2728_);
lean_dec_ref(v___f_2724_);
lean_del_object(v___x_2707_);
lean_dec(v_fst_2705_);
v_a_2749_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___x_2729_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2729_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2763_, lean_object* v___x_2764_, lean_object* v_as_2765_, lean_object* v_sz_2766_, lean_object* v_i_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
size_t v_sz_boxed_2774_; size_t v_i_boxed_2775_; lean_object* v_res_2776_; 
v_sz_boxed_2774_ = lean_unbox_usize(v_sz_2766_);
lean_dec(v_sz_2766_);
v_i_boxed_2775_ = lean_unbox_usize(v_i_2767_);
lean_dec(v_i_2767_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2763_, v___x_2764_, v_as_2765_, v_sz_boxed_2774_, v_i_boxed_2775_, v_b_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec_ref(v_as_2765_);
lean_dec(v___x_2764_);
lean_dec(v___x_2763_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2777_, size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_b_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = lean_usize_dec_lt(v_i_2779_, v_sz_2778_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_b_2780_);
return v___x_2787_;
}
else
{
lean_object* v_a_2788_; lean_object* v_toInductionSubgoal_2789_; lean_object* v_mvarId_2790_; uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_a_2788_ = lean_array_uget_borrowed(v_as_2777_, v_i_2779_);
v_toInductionSubgoal_2789_ = lean_ctor_get(v_a_2788_, 0);
v_mvarId_2790_ = lean_ctor_get(v_toInductionSubgoal_2789_, 0);
v___x_2791_ = 0;
v___x_2792_ = lean_box(0);
lean_inc(v_mvarId_2790_);
v___x_2793_ = l_Lean_MVarId_refl(v_mvarId_2790_, v___x_2791_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2793_) == 0)
{
size_t v___x_2794_; size_t v___x_2795_; 
lean_dec_ref_known(v___x_2793_, 1);
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = lean_usize_add(v_i_2779_, v___x_2794_);
v_i_2779_ = v___x_2795_;
v_b_2780_ = v___x_2792_;
goto _start;
}
else
{
return v___x_2793_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2797_, lean_object* v_sz_2798_, lean_object* v_i_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
size_t v_sz_boxed_2806_; size_t v_i_boxed_2807_; lean_object* v_res_2808_; 
v_sz_boxed_2806_ = lean_unbox_usize(v_sz_2798_);
lean_dec(v_sz_2798_);
v_i_boxed_2807_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_res_2808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2797_, v_sz_boxed_2806_, v_i_boxed_2807_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_as_2797_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2809_, lean_object* v_tail_2810_, lean_object* v_recName_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v_val_2823_, uint8_t v___x_2824_, lean_object* v_brecOnGoName_2825_, lean_object* v_levelParams_2826_, lean_object* v___x_2827_, lean_object* v_brecOnName_2828_, lean_object* v___x_2829_, lean_object* v_brecOnEqName_2830_, lean_object* v_fs_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; size_t v_sz_2841_; size_t v___x_2842_; lean_object* v___x_2843_; 
lean_inc(v___x_2809_);
v___x_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2809_);
lean_ctor_set(v___x_2837_, 1, v_tail_2810_);
v___x_2838_ = l_Lean_Expr_const___override(v_recName_2811_, v___x_2837_);
v___x_2839_ = l_Lean_mkAppN(v___x_2838_, v___x_2812_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2839_);
lean_ctor_set(v___x_2840_, 1, v___x_2813_);
v_sz_2841_ = lean_array_size(v___x_2814_);
v___x_2842_ = ((size_t)0ULL);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2815_, v___x_2816_, v___x_2814_, v_sz_2841_, v___x_2842_, v___x_2840_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_fst_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_3210_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v_fst_2845_ = lean_ctor_get(v_a_2844_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_a_2844_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_a_2844_, 1);
lean_dec(v_unused_3211_);
v___x_2847_ = v_a_2844_;
v_isShared_2848_ = v_isSharedCheck_3210_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_fst_2845_);
lean_dec(v_a_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_3210_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
size_t v_sz_2849_; lean_object* v___x_2850_; 
v_sz_2849_ = lean_array_size(v___x_2817_);
lean_inc_ref(v_fs_2831_);
lean_inc_ref(v___x_2818_);
lean_inc_ref(v___x_2814_);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2809_, v___x_2814_, v___x_2818_, v_fs_2831_, v___x_2817_, v_sz_2849_, v___x_2842_, v_fst_2845_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l_Lean_mkAppN(v_a_2851_, v___x_2819_);
lean_inc_ref_n(v___x_2820_, 3);
v___x_2853_ = l_Lean_Expr_app___override(v___x_2852_, v___x_2820_);
v___x_2854_ = l_Array_append___redArg(v___x_2812_, v___x_2814_);
v___x_2855_ = l_Array_append___redArg(v___x_2854_, v___x_2819_);
v___x_2856_ = lean_mk_empty_array_with_capacity(v___x_2821_);
v___x_2857_ = lean_array_push(v___x_2856_, v___x_2820_);
v___x_2858_ = l_Array_append___redArg(v___x_2855_, v___x_2857_);
lean_dec_ref(v___x_2857_);
v___x_2859_ = l_Array_append___redArg(v___x_2858_, v_fs_2831_);
v___x_2860_ = lean_array_get(v___x_2822_, v___x_2814_, v_val_2823_);
lean_dec_ref(v___x_2814_);
v___x_2861_ = lean_array_push(v___x_2819_, v___x_2820_);
v___x_2862_ = l_Lean_mkAppN(v___x_2860_, v___x_2861_);
v___x_2863_ = lean_array_get(v___x_2822_, v___x_2818_, v_val_2823_);
lean_dec_ref(v___x_2818_);
v___x_2864_ = l_Lean_mkAppN(v___x_2863_, v___x_2861_);
lean_inc_ref(v___x_2862_);
v___x_2865_ = l_Lean_Meta_mkPProd(v___x_2862_, v___x_2864_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; uint8_t v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = 0;
v___x_2868_ = 1;
v___x_2869_ = l_Lean_Meta_mkForallFVars(v___x_2859_, v_a_2866_, v___x_2867_, v___x_2824_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = l_Lean_Meta_mkLambdaFVars(v___x_2859_, v___x_2853_, v___x_2867_, v___x_2824_, v___x_2867_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_3177_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = lean_box(1);
lean_inc(v_levelParams_2826_);
lean_inc(v_brecOnGoName_2825_);
v___x_2874_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2825_, v_levelParams_2826_, v_a_2870_, v_a_2872_, v___x_2873_, v___y_2835_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_3177_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_3177_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
lean_inc(v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set_tag(v___x_2877_, 1);
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_3176_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_addDecl(v___x_2880_, v___x_2867_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_toConstantVal_2882_; lean_object* v_name_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref_known(v___x_2881_, 1);
v_toConstantVal_2882_ = lean_ctor_get(v_a_2875_, 0);
lean_inc_ref(v_toConstantVal_2882_);
lean_dec(v_a_2875_);
v_name_2883_ = lean_ctor_get(v_toConstantVal_2882_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_toConstantVal_2882_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; lean_object* v_unused_3175_; 
v_unused_3174_ = lean_ctor_get(v_toConstantVal_2882_, 2);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_toConstantVal_2882_, 1);
lean_dec(v_unused_3175_);
v___x_2885_ = v_toConstantVal_2882_;
v_isShared_2886_ = v_isSharedCheck_3173_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_name_2883_);
lean_dec(v_toConstantVal_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_3173_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_env_2889_; lean_object* v_nextMacroScope_2890_; lean_object* v_ngen_2891_; lean_object* v_auxDeclNGen_2892_; lean_object* v_traceState_2893_; lean_object* v_recordedDeps_2894_; lean_object* v_messages_2895_; lean_object* v_infoState_2896_; lean_object* v_snapshotTasks_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_3171_; 
lean_inc(v_name_2883_);
v___x_2887_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2883_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec_ref(v___x_2887_);
v___x_2888_ = lean_st_ref_take(v___y_2835_);
v_env_2889_ = lean_ctor_get(v___x_2888_, 0);
v_nextMacroScope_2890_ = lean_ctor_get(v___x_2888_, 1);
v_ngen_2891_ = lean_ctor_get(v___x_2888_, 2);
v_auxDeclNGen_2892_ = lean_ctor_get(v___x_2888_, 3);
v_traceState_2893_ = lean_ctor_get(v___x_2888_, 4);
v_recordedDeps_2894_ = lean_ctor_get(v___x_2888_, 6);
v_messages_2895_ = lean_ctor_get(v___x_2888_, 7);
v_infoState_2896_ = lean_ctor_get(v___x_2888_, 8);
v_snapshotTasks_2897_ = lean_ctor_get(v___x_2888_, 9);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v___x_2888_, 5);
lean_dec(v_unused_3172_);
v___x_2899_ = v___x_2888_;
v_isShared_2900_ = v_isSharedCheck_3171_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_snapshotTasks_2897_);
lean_inc(v_infoState_2896_);
lean_inc(v_messages_2895_);
lean_inc(v_recordedDeps_2894_);
lean_inc(v_traceState_2893_);
lean_inc(v_auxDeclNGen_2892_);
lean_inc(v_ngen_2891_);
lean_inc(v_nextMacroScope_2890_);
lean_inc(v_env_2889_);
lean_dec(v___x_2888_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_3171_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2901_ = l_Lean_addProtected(v_env_2889_, v_name_2883_);
v___x_2902_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 5, v___x_2902_);
lean_ctor_set(v___x_2899_, 0, v___x_2901_);
v___x_2904_ = v___x_2899_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_nextMacroScope_2890_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_ngen_2891_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_auxDeclNGen_2892_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_traceState_2893_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3170_, 6, v_recordedDeps_2894_);
lean_ctor_set(v_reuseFailAlloc_3170_, 7, v_messages_2895_);
lean_ctor_set(v_reuseFailAlloc_3170_, 8, v_infoState_2896_);
lean_ctor_set(v_reuseFailAlloc_3170_, 9, v_snapshotTasks_2897_);
v___x_2904_ = v_reuseFailAlloc_3170_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_mctx_2907_; lean_object* v_zetaDeltaFVarIds_2908_; lean_object* v_postponed_2909_; lean_object* v_diag_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_3168_; 
v___x_2905_ = lean_st_ref_put(v___y_2835_, v___x_2904_);
v___x_2906_ = lean_st_ref_take(v___y_2833_);
v_mctx_2907_ = lean_ctor_get(v___x_2906_, 0);
v_zetaDeltaFVarIds_2908_ = lean_ctor_get(v___x_2906_, 2);
v_postponed_2909_ = lean_ctor_get(v___x_2906_, 3);
v_diag_2910_ = lean_ctor_get(v___x_2906_, 4);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_2906_, 1);
lean_dec(v_unused_3169_);
v___x_2912_ = v___x_2906_;
v_isShared_2913_ = v_isSharedCheck_3168_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_diag_2910_);
lean_inc(v_postponed_2909_);
lean_inc(v_zetaDeltaFVarIds_2908_);
lean_inc(v_mctx_2907_);
lean_dec(v___x_2906_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_3168_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2914_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___x_2914_);
v___x_2916_ = v___x_2912_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_mctx_2907_);
lean_ctor_set(v_reuseFailAlloc_3167_, 1, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3167_, 2, v_zetaDeltaFVarIds_2908_);
lean_ctor_set(v_reuseFailAlloc_3167_, 3, v_postponed_2909_);
lean_ctor_set(v_reuseFailAlloc_3167_, 4, v_diag_2910_);
v___x_2916_ = v_reuseFailAlloc_3167_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2917_ = lean_st_ref_put(v___y_2833_, v___x_2916_);
lean_inc(v___x_2827_);
v___x_2918_ = l_Lean_Expr_const___override(v_brecOnGoName_2825_, v___x_2827_);
v___x_2919_ = l_Lean_mkAppN(v___x_2918_, v___x_2859_);
lean_inc_ref(v___x_2919_);
v___x_2920_ = l_Lean_Meta_mkPProdFstM(v___x_2919_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = l_Lean_Meta_mkLambdaFVars(v___x_2859_, v_a_2921_, v___x_2867_, v___x_2824_, v___x_2867_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2924_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
v___x_2924_ = l_Lean_Meta_mkForallFVars(v___x_2859_, v___x_2862_, v___x_2867_, v___x_2824_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_3142_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
lean_inc(v_levelParams_2826_);
v___x_2926_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2828_, v_levelParams_2826_, v_a_2925_, v_a_2923_, v___x_2873_, v___y_2835_);
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_3142_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_3142_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
lean_inc(v_a_2927_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 1);
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_3141_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_addDecl(v___x_2932_, v___x_2867_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_toConstantVal_2934_; lean_object* v_name_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref_known(v___x_2933_, 1);
v_toConstantVal_2934_ = lean_ctor_get(v_a_2927_, 0);
lean_inc_ref(v_toConstantVal_2934_);
lean_dec(v_a_2927_);
v_name_2935_ = lean_ctor_get(v_toConstantVal_2934_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_toConstantVal_2934_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; lean_object* v_unused_3140_; 
v_unused_3139_ = lean_ctor_get(v_toConstantVal_2934_, 2);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_toConstantVal_2934_, 1);
lean_dec(v_unused_3140_);
v___x_2937_ = v_toConstantVal_2934_;
v_isShared_2938_ = v_isSharedCheck_3138_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_name_2935_);
lean_dec(v_toConstantVal_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3138_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_env_2941_; lean_object* v_nextMacroScope_2942_; lean_object* v_ngen_2943_; lean_object* v_auxDeclNGen_2944_; lean_object* v_traceState_2945_; lean_object* v_recordedDeps_2946_; lean_object* v_messages_2947_; lean_object* v_infoState_2948_; lean_object* v_snapshotTasks_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3136_; 
lean_inc(v_name_2935_);
v___x_2939_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2935_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec_ref(v___x_2939_);
v___x_2940_ = lean_st_ref_take(v___y_2835_);
v_env_2941_ = lean_ctor_get(v___x_2940_, 0);
v_nextMacroScope_2942_ = lean_ctor_get(v___x_2940_, 1);
v_ngen_2943_ = lean_ctor_get(v___x_2940_, 2);
v_auxDeclNGen_2944_ = lean_ctor_get(v___x_2940_, 3);
v_traceState_2945_ = lean_ctor_get(v___x_2940_, 4);
v_recordedDeps_2946_ = lean_ctor_get(v___x_2940_, 6);
v_messages_2947_ = lean_ctor_get(v___x_2940_, 7);
v_infoState_2948_ = lean_ctor_get(v___x_2940_, 8);
v_snapshotTasks_2949_ = lean_ctor_get(v___x_2940_, 9);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_2940_, 5);
lean_dec(v_unused_3137_);
v___x_2951_ = v___x_2940_;
v_isShared_2952_ = v_isSharedCheck_3136_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snapshotTasks_2949_);
lean_inc(v_infoState_2948_);
lean_inc(v_messages_2947_);
lean_inc(v_recordedDeps_2946_);
lean_inc(v_traceState_2945_);
lean_inc(v_auxDeclNGen_2944_);
lean_inc(v_ngen_2943_);
lean_inc(v_nextMacroScope_2942_);
lean_inc(v_env_2941_);
lean_dec(v___x_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3136_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
lean_inc(v_name_2935_);
v___x_2953_ = l_Lean_markAuxRecursor(v_env_2941_, v_name_2935_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 5, v___x_2902_);
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_nextMacroScope_2942_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_ngen_2943_);
lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_auxDeclNGen_2944_);
lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_traceState_2945_);
lean_ctor_set(v_reuseFailAlloc_3135_, 5, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3135_, 6, v_recordedDeps_2946_);
lean_ctor_set(v_reuseFailAlloc_3135_, 7, v_messages_2947_);
lean_ctor_set(v_reuseFailAlloc_3135_, 8, v_infoState_2948_);
lean_ctor_set(v_reuseFailAlloc_3135_, 9, v_snapshotTasks_2949_);
v___x_2955_ = v_reuseFailAlloc_3135_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v_mctx_2958_; lean_object* v_zetaDeltaFVarIds_2959_; lean_object* v_postponed_2960_; lean_object* v_diag_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3133_; 
v___x_2956_ = lean_st_ref_put(v___y_2835_, v___x_2955_);
v___x_2957_ = lean_st_ref_take(v___y_2833_);
v_mctx_2958_ = lean_ctor_get(v___x_2957_, 0);
v_zetaDeltaFVarIds_2959_ = lean_ctor_get(v___x_2957_, 2);
v_postponed_2960_ = lean_ctor_get(v___x_2957_, 3);
v_diag_2961_ = lean_ctor_get(v___x_2957_, 4);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_2957_, 1);
lean_dec(v_unused_3134_);
v___x_2963_ = v___x_2957_;
v_isShared_2964_ = v_isSharedCheck_3133_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_diag_2961_);
lean_inc(v_postponed_2960_);
lean_inc(v_zetaDeltaFVarIds_2959_);
lean_inc(v_mctx_2958_);
lean_dec(v___x_2957_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3133_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2914_);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_mctx_2958_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_zetaDeltaFVarIds_2959_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_postponed_2960_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_diag_2961_);
v___x_2966_ = v_reuseFailAlloc_3132_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_env_2969_; lean_object* v_nextMacroScope_2970_; lean_object* v_ngen_2971_; lean_object* v_auxDeclNGen_2972_; lean_object* v_traceState_2973_; lean_object* v_recordedDeps_2974_; lean_object* v_messages_2975_; lean_object* v_infoState_2976_; lean_object* v_snapshotTasks_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3130_; 
v___x_2967_ = lean_st_ref_put(v___y_2833_, v___x_2966_);
v___x_2968_ = lean_st_ref_take(v___y_2835_);
v_env_2969_ = lean_ctor_get(v___x_2968_, 0);
v_nextMacroScope_2970_ = lean_ctor_get(v___x_2968_, 1);
v_ngen_2971_ = lean_ctor_get(v___x_2968_, 2);
v_auxDeclNGen_2972_ = lean_ctor_get(v___x_2968_, 3);
v_traceState_2973_ = lean_ctor_get(v___x_2968_, 4);
v_recordedDeps_2974_ = lean_ctor_get(v___x_2968_, 6);
v_messages_2975_ = lean_ctor_get(v___x_2968_, 7);
v_infoState_2976_ = lean_ctor_get(v___x_2968_, 8);
v_snapshotTasks_2977_ = lean_ctor_get(v___x_2968_, 9);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_2968_, 5);
lean_dec(v_unused_3131_);
v___x_2979_ = v___x_2968_;
v_isShared_2980_ = v_isSharedCheck_3130_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_snapshotTasks_2977_);
lean_inc(v_infoState_2976_);
lean_inc(v_messages_2975_);
lean_inc(v_recordedDeps_2974_);
lean_inc(v_traceState_2973_);
lean_inc(v_auxDeclNGen_2972_);
lean_inc(v_ngen_2971_);
lean_inc(v_nextMacroScope_2970_);
lean_inc(v_env_2969_);
lean_dec(v___x_2968_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3130_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_inc(v_name_2935_);
v___x_2981_ = l_Lean_addProtected(v_env_2969_, v_name_2935_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 5, v___x_2902_);
lean_ctor_set(v___x_2979_, 0, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_nextMacroScope_2970_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_ngen_2971_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v_auxDeclNGen_2972_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v_traceState_2973_);
lean_ctor_set(v_reuseFailAlloc_3129_, 5, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3129_, 6, v_recordedDeps_2974_);
lean_ctor_set(v_reuseFailAlloc_3129_, 7, v_messages_2975_);
lean_ctor_set(v_reuseFailAlloc_3129_, 8, v_infoState_2976_);
lean_ctor_set(v_reuseFailAlloc_3129_, 9, v_snapshotTasks_2977_);
v___x_2983_ = v_reuseFailAlloc_3129_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_mctx_2986_; lean_object* v_zetaDeltaFVarIds_2987_; lean_object* v_postponed_2988_; lean_object* v_diag_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3127_; 
v___x_2984_ = lean_st_ref_put(v___y_2835_, v___x_2983_);
v___x_2985_ = lean_st_ref_take(v___y_2833_);
v_mctx_2986_ = lean_ctor_get(v___x_2985_, 0);
v_zetaDeltaFVarIds_2987_ = lean_ctor_get(v___x_2985_, 2);
v_postponed_2988_ = lean_ctor_get(v___x_2985_, 3);
v_diag_2989_ = lean_ctor_get(v___x_2985_, 4);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_2985_, 1);
lean_dec(v_unused_3128_);
v___x_2991_ = v___x_2985_;
v_isShared_2992_ = v_isSharedCheck_3127_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_diag_2989_);
lean_inc(v_postponed_2988_);
lean_inc(v_zetaDeltaFVarIds_2987_);
lean_inc(v_mctx_2986_);
lean_dec(v___x_2985_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3127_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_2914_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_mctx_2986_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_zetaDeltaFVarIds_2987_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_postponed_2988_);
lean_ctor_set(v_reuseFailAlloc_3126_, 4, v_diag_2989_);
v___x_2994_ = v_reuseFailAlloc_3126_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2995_ = lean_st_ref_put(v___y_2833_, v___x_2994_);
v___x_2996_ = l_Lean_Expr_const___override(v_name_2935_, v___x_2827_);
v___x_2997_ = l_Lean_mkAppN(v___x_2996_, v___x_2859_);
v___x_2998_ = lean_array_get(v___x_2822_, v_fs_2831_, v_val_2823_);
lean_dec_ref(v_fs_2831_);
v___x_2999_ = l_Lean_mkAppN(v___x_2998_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_3000_ = l_Lean_Meta_mkPProdSndM(v___x_2919_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = l_Lean_Expr_app___override(v___x_2999_, v_a_3001_);
v___x_3003_ = l_Lean_Meta_mkEq(v___x_2997_, v___x_3002_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc_n(v_a_3004_, 2);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_box(0);
v___x_3006_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3004_, v___x_3005_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_Expr_mvarId_x21(v_a_3007_);
v___x_3009_ = l_Lean_Expr_fvarId_x21(v___x_2820_);
lean_dec_ref(v___x_2820_);
v___x_3010_ = lean_mk_empty_array_with_capacity(v___x_2829_);
v___x_3011_ = lean_box(0);
v___x_3012_ = l_Lean_MVarId_cases(v___x_3008_, v___x_3009_, v___x_3010_, v___x_2867_, v___x_3011_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; size_t v_sz_3015_; lean_object* v___x_3016_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_box(0);
v_sz_3015_ = lean_array_size(v_a_3013_);
v___x_3016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3013_, v_sz_3015_, v___x_2842_, v___x_3014_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v_a_3013_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v___x_3017_; lean_object* v_a_3018_; lean_object* v___x_3019_; 
lean_dec_ref_known(v___x_3016_, 1);
v___x_3017_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3007_, v___y_2833_);
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Lean_Meta_mkForallFVars(v___x_2859_, v_a_3004_, v___x_2867_, v___x_2824_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_Meta_mkLambdaFVars(v___x_2859_, v_a_3018_, v___x_2867_, v___x_2824_, v___x_2867_, v___x_2824_, v___x_2868_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec_ref(v___x_2859_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3024_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
lean_inc(v_brecOnEqName_2830_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 2, v_a_3020_);
lean_ctor_set(v___x_2937_, 1, v_levelParams_2826_);
lean_ctor_set(v___x_2937_, 0, v_brecOnEqName_2830_);
v___x_3024_ = v___x_2937_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_brecOnEqName_2830_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v_levelParams_2826_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_a_3020_);
v___x_3024_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___x_3025_ = lean_box(0);
lean_inc(v_brecOnEqName_2830_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 1);
lean_ctor_set(v___x_2847_, 1, v___x_3025_);
lean_ctor_set(v___x_2847_, 0, v_brecOnEqName_2830_);
v___x_3027_ = v___x_2847_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_brecOnEqName_2830_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3029_; 
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 2, v___x_3027_);
lean_ctor_set(v___x_2885_, 1, v_a_3022_);
lean_ctor_set(v___x_2885_, 0, v___x_3024_);
v___x_3029_ = v___x_2885_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_a_3022_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3030_; lean_object* v_a_3031_; lean_object* v___x_3032_; 
v___x_3030_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3029_, v___y_2835_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = l_Lean_addDecl(v_a_3031_, v___x_2867_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3073_; 
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3032_, 0);
lean_dec(v_unused_3074_);
v___x_3034_ = v___x_3032_;
v_isShared_3035_ = v_isSharedCheck_3073_;
goto v_resetjp_3033_;
}
else
{
lean_dec(v___x_3032_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3073_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v_env_3037_; lean_object* v_nextMacroScope_3038_; lean_object* v_ngen_3039_; lean_object* v_auxDeclNGen_3040_; lean_object* v_traceState_3041_; lean_object* v_recordedDeps_3042_; lean_object* v_messages_3043_; lean_object* v_infoState_3044_; lean_object* v_snapshotTasks_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3071_; 
v___x_3036_ = lean_st_ref_take(v___y_2835_);
v_env_3037_ = lean_ctor_get(v___x_3036_, 0);
v_nextMacroScope_3038_ = lean_ctor_get(v___x_3036_, 1);
v_ngen_3039_ = lean_ctor_get(v___x_3036_, 2);
v_auxDeclNGen_3040_ = lean_ctor_get(v___x_3036_, 3);
v_traceState_3041_ = lean_ctor_get(v___x_3036_, 4);
v_recordedDeps_3042_ = lean_ctor_get(v___x_3036_, 6);
v_messages_3043_ = lean_ctor_get(v___x_3036_, 7);
v_infoState_3044_ = lean_ctor_get(v___x_3036_, 8);
v_snapshotTasks_3045_ = lean_ctor_get(v___x_3036_, 9);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3036_, 5);
lean_dec(v_unused_3072_);
v___x_3047_ = v___x_3036_;
v_isShared_3048_ = v_isSharedCheck_3071_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_snapshotTasks_3045_);
lean_inc(v_infoState_3044_);
lean_inc(v_messages_3043_);
lean_inc(v_recordedDeps_3042_);
lean_inc(v_traceState_3041_);
lean_inc(v_auxDeclNGen_3040_);
lean_inc(v_ngen_3039_);
lean_inc(v_nextMacroScope_3038_);
lean_inc(v_env_3037_);
lean_dec(v___x_3036_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3071_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3049_ = l_Lean_addProtected(v_env_3037_, v_brecOnEqName_2830_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 5, v___x_2902_);
lean_ctor_set(v___x_3047_, 0, v___x_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_nextMacroScope_3038_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_ngen_3039_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_auxDeclNGen_3040_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_traceState_3041_);
lean_ctor_set(v_reuseFailAlloc_3070_, 5, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3070_, 6, v_recordedDeps_3042_);
lean_ctor_set(v_reuseFailAlloc_3070_, 7, v_messages_3043_);
lean_ctor_set(v_reuseFailAlloc_3070_, 8, v_infoState_3044_);
lean_ctor_set(v_reuseFailAlloc_3070_, 9, v_snapshotTasks_3045_);
v___x_3051_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_mctx_3054_; lean_object* v_zetaDeltaFVarIds_3055_; lean_object* v_postponed_3056_; lean_object* v_diag_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3068_; 
v___x_3052_ = lean_st_ref_put(v___y_2835_, v___x_3051_);
v___x_3053_ = lean_st_ref_take(v___y_2833_);
v_mctx_3054_ = lean_ctor_get(v___x_3053_, 0);
v_zetaDeltaFVarIds_3055_ = lean_ctor_get(v___x_3053_, 2);
v_postponed_3056_ = lean_ctor_get(v___x_3053_, 3);
v_diag_3057_ = lean_ctor_get(v___x_3053_, 4);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_3053_, 1);
lean_dec(v_unused_3069_);
v___x_3059_ = v___x_3053_;
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_diag_3057_);
lean_inc(v_postponed_3056_);
lean_inc(v_zetaDeltaFVarIds_3055_);
lean_inc(v_mctx_3054_);
lean_dec(v___x_3053_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v___x_2914_);
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_mctx_3054_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_zetaDeltaFVarIds_3055_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_postponed_3056_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v_diag_3057_);
v___x_3062_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_st_ref_put(v___y_2833_, v___x_3062_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3014_);
v___x_3065_ = v___x_3034_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3014_);
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
}
}
else
{
lean_dec(v_brecOnEqName_2830_);
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v_a_3020_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
v_a_3078_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3021_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3021_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
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
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3018_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
v_a_3086_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3019_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3019_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
return v___x_3016_;
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3004_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
v_a_3094_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3012_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3012_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v_a_3004_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3102_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3006_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3006_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3110_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3003_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3003_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v___x_2999_);
lean_dec_ref(v___x_2997_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3118_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3000_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3000_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
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
lean_dec(v_a_2927_);
lean_dec_ref(v___x_2919_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
return v___x_2933_;
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v_a_2923_);
lean_dec_ref(v___x_2919_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3143_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_2924_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_2924_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v___x_2919_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3151_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_2922_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_2922_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v___x_2919_);
lean_del_object(v___x_2885_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec_ref(v___x_2820_);
v_a_3159_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_2920_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_2920_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
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
lean_dec(v_a_2875_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec(v_a_2870_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
v_a_3178_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_2871_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_2871_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
v_a_3186_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_2869_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_2869_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
v_a_3194_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_2865_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_2865_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_del_object(v___x_2847_);
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___x_2812_);
v_a_3202_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_2850_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_2850_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec_ref(v_fs_2831_);
lean_dec(v_brecOnEqName_2830_);
lean_dec(v_brecOnName_2828_);
lean_dec(v___x_2827_);
lean_dec(v_levelParams_2826_);
lean_dec(v_brecOnGoName_2825_);
lean_dec_ref(v___x_2820_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___x_2812_);
lean_dec(v___x_2809_);
v_a_3212_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_2843_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_2843_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3220_ = _args[0];
lean_object* v_tail_3221_ = _args[1];
lean_object* v_recName_3222_ = _args[2];
lean_object* v___x_3223_ = _args[3];
lean_object* v___x_3224_ = _args[4];
lean_object* v___x_3225_ = _args[5];
lean_object* v___x_3226_ = _args[6];
lean_object* v___x_3227_ = _args[7];
lean_object* v___x_3228_ = _args[8];
lean_object* v___x_3229_ = _args[9];
lean_object* v___x_3230_ = _args[10];
lean_object* v___x_3231_ = _args[11];
lean_object* v___x_3232_ = _args[12];
lean_object* v___x_3233_ = _args[13];
lean_object* v_val_3234_ = _args[14];
lean_object* v___x_3235_ = _args[15];
lean_object* v_brecOnGoName_3236_ = _args[16];
lean_object* v_levelParams_3237_ = _args[17];
lean_object* v___x_3238_ = _args[18];
lean_object* v_brecOnName_3239_ = _args[19];
lean_object* v___x_3240_ = _args[20];
lean_object* v_brecOnEqName_3241_ = _args[21];
lean_object* v_fs_3242_ = _args[22];
lean_object* v___y_3243_ = _args[23];
lean_object* v___y_3244_ = _args[24];
lean_object* v___y_3245_ = _args[25];
lean_object* v___y_3246_ = _args[26];
lean_object* v___y_3247_ = _args[27];
_start:
{
uint8_t v___x_30851__boxed_3248_; lean_object* v_res_3249_; 
v___x_30851__boxed_3248_ = lean_unbox(v___x_3235_);
v_res_3249_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3220_, v_tail_3221_, v_recName_3222_, v___x_3223_, v___x_3224_, v___x_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v___x_3231_, v___x_3232_, v___x_3233_, v_val_3234_, v___x_30851__boxed_3248_, v_brecOnGoName_3236_, v_levelParams_3237_, v___x_3238_, v_brecOnName_3239_, v___x_3240_, v_brecOnEqName_3241_, v_fs_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___x_3240_);
lean_dec(v_val_3234_);
lean_dec_ref(v___x_3233_);
lean_dec(v___x_3232_);
lean_dec_ref(v___x_3228_);
lean_dec(v___x_3227_);
lean_dec(v___x_3226_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3250_, lean_object* v_a_3251_, uint8_t v___x_3252_, lean_object* v_f_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; 
lean_inc_ref(v_targs_3250_);
v___x_3259_ = lean_array_push(v_targs_3250_, v_f_3253_);
v___x_3260_ = l_Lean_mkAppN(v_a_3251_, v_targs_3250_);
lean_dec_ref(v_targs_3250_);
v___x_3261_ = 0;
v___x_3262_ = 1;
v___x_3263_ = l_Lean_Meta_mkForallFVars(v___x_3259_, v___x_3260_, v___x_3261_, v___x_3252_, v___x_3252_, v___x_3262_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec_ref(v___x_3259_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3264_, lean_object* v_a_3265_, lean_object* v___x_3266_, lean_object* v_f_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___x_31565__boxed_3273_; lean_object* v_res_3274_; 
v___x_31565__boxed_3273_ = lean_unbox(v___x_3266_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3264_, v_a_3265_, v___x_31565__boxed_3273_, v_f_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3278_, uint8_t v___x_3279_, lean_object* v___x_3280_, lean_object* v_targs_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = lean_box(v___x_3279_);
lean_inc_ref(v_targs_3281_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3289_, 0, v_targs_3281_);
lean_closure_set(v___f_3289_, 1, v_a_3278_);
lean_closure_set(v___f_3289_, 2, v___x_3288_);
v___x_3290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3291_ = l_Lean_mkAppN(v___x_3280_, v_targs_3281_);
lean_dec_ref(v_targs_3281_);
v___x_3292_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3290_, v___x_3291_, v___f_3289_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3293_, lean_object* v___x_3294_, lean_object* v___x_3295_, lean_object* v_targs_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v___x_31599__boxed_3303_; lean_object* v_res_3304_; 
v___x_31599__boxed_3303_ = lean_unbox(v___x_3294_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3293_, v___x_31599__boxed_3303_, v___x_3295_, v_targs_3296_, v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec_ref(v_x_3297_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3305_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_x_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v_as_3324_, size_t v_sz_3325_, size_t v_i_3326_, lean_object* v_b_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
uint8_t v___x_3333_; 
v___x_3333_ = lean_usize_dec_lt(v_i_3326_, v_sz_3325_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v_b_3327_);
return v___x_3334_;
}
else
{
lean_object* v_snd_3335_; lean_object* v_fst_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3433_; 
v_snd_3335_ = lean_ctor_get(v_b_3327_, 1);
v_fst_3336_ = lean_ctor_get(v_b_3327_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_b_3327_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3338_ = v_b_3327_;
v_isShared_3339_ = v_isSharedCheck_3433_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_snd_3335_);
lean_inc(v_fst_3336_);
lean_dec(v_b_3327_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3433_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fst_3340_; lean_object* v_snd_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3432_; 
v_fst_3340_ = lean_ctor_get(v_snd_3335_, 0);
v_snd_3341_ = lean_ctor_get(v_snd_3335_, 1);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_snd_3335_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3343_ = v_snd_3335_;
v_isShared_3344_ = v_isSharedCheck_3432_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_snd_3341_);
lean_inc(v_fst_3340_);
lean_dec(v_snd_3335_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3432_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v_next_3353_; 
v_next_3353_ = lean_ctor_get(v_snd_3341_, 0);
lean_inc(v_next_3353_);
if (lean_obj_tag(v_next_3353_) == 0)
{
goto v___jp_3345_;
}
else
{
lean_object* v_upperBound_3354_; lean_object* v_val_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3431_; 
v_upperBound_3354_ = lean_ctor_get(v_snd_3341_, 1);
v_val_3355_ = lean_ctor_get(v_next_3353_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_next_3353_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3357_ = v_next_3353_;
v_isShared_3358_ = v_isSharedCheck_3431_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_val_3355_);
lean_dec(v_next_3353_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3431_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
uint8_t v___x_3359_; 
v___x_3359_ = lean_nat_dec_lt(v_val_3355_, v_upperBound_3354_);
if (v___x_3359_ == 0)
{
lean_del_object(v___x_3357_);
lean_dec(v_val_3355_);
goto v___jp_3345_;
}
else
{
lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3428_; 
lean_inc(v_upperBound_3354_);
lean_del_object(v___x_3343_);
lean_del_object(v___x_3338_);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_snd_3341_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3429_ = lean_ctor_get(v_snd_3341_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_snd_3341_, 0);
lean_dec(v_unused_3430_);
v___x_3361_ = v_snd_3341_;
v_isShared_3362_ = v_isSharedCheck_3428_;
goto v_resetjp_3360_;
}
else
{
lean_dec(v_snd_3341_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3428_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v_array_3363_; lean_object* v_start_3364_; lean_object* v_stop_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v_array_3363_ = lean_ctor_get(v_fst_3340_, 0);
v_start_3364_ = lean_ctor_get(v_fst_3340_, 1);
v_stop_3365_ = lean_ctor_get(v_fst_3340_, 2);
v___x_3366_ = lean_unsigned_to_nat(1u);
v___x_3367_ = lean_nat_add(v_val_3355_, v___x_3366_);
lean_dec(v_val_3355_);
lean_inc(v___x_3367_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3369_ = v___x_3357_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3369_);
v___x_3371_ = v___x_3361_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_upperBound_3354_);
v___x_3371_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_nat_dec_lt(v_start_3364_, v_stop_3365_);
if (v___x_3372_ == 0)
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec(v___x_3367_);
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v_fst_3340_);
lean_ctor_set(v___x_3373_, 1, v___x_3371_);
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_fst_3336_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_stop_3365_);
lean_inc(v_start_3364_);
lean_inc_ref(v_array_3363_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_fst_3340_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; lean_object* v_unused_3425_; 
v_unused_3423_ = lean_ctor_get(v_fst_3340_, 2);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_fst_3340_, 1);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_fst_3340_, 0);
lean_dec(v_unused_3425_);
v___x_3377_ = v_fst_3340_;
v_isShared_3378_ = v_isSharedCheck_3422_;
goto v_resetjp_3376_;
}
else
{
lean_dec(v_fst_3340_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3422_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v___x_3379_; lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___f_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3379_ = lean_nat_dec_lt(v___x_3322_, v___x_3323_);
v_a_3380_ = lean_array_uget_borrowed(v_as_3324_, v_i_3326_);
v___x_3381_ = lean_array_fget_borrowed(v_array_3363_, v_start_3364_);
v___x_3382_ = lean_box(v___x_3379_);
lean_inc(v___x_3381_);
lean_inc(v_a_3380_);
v___f_3383_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3383_, 0, v_a_3380_);
lean_closure_set(v___f_3383_, 1, v___x_3382_);
lean_closure_set(v___f_3383_, 2, v___x_3381_);
v___x_3384_ = lean_nat_add(v_start_3364_, v___x_3366_);
lean_dec(v_start_3364_);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v___x_3384_);
v___x_3386_ = v___x_3377_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_array_3363_);
lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3421_, 2, v_stop_3365_);
v___x_3386_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3387_; 
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc(v_a_3380_);
v___x_3387_ = lean_infer_type(v_a_3380_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = 0;
v___x_3390_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3388_, v___f_3383_, v___x_3389_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; size_t v___x_3402_; size_t v___x_3403_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___f_3392_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3392_, 0, v_a_3391_);
v___x_3393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3394_ = l_Nat_reprFast(v___x_3367_);
v___x_3395_ = lean_string_append(v___x_3393_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = lean_box(0);
v___x_3397_ = l_Lean_Name_str___override(v___x_3396_, v___x_3395_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___f_3392_);
v___x_3399_ = lean_array_push(v_fst_3336_, v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3386_);
lean_ctor_set(v___x_3400_, 1, v___x_3371_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3326_, v___x_3402_);
v_i_3326_ = v___x_3403_;
v_b_3327_ = v___x_3401_;
goto _start;
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec_ref(v___x_3386_);
lean_dec_ref(v___x_3371_);
lean_dec(v___x_3367_);
lean_dec(v_fst_3336_);
v_a_3405_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3390_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3390_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v___x_3386_);
lean_dec_ref(v___f_3383_);
lean_dec_ref(v___x_3371_);
lean_dec(v___x_3367_);
lean_dec(v_fst_3336_);
v_a_3413_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3387_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3387_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
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
v___jp_3345_:
{
lean_object* v___x_3347_; 
if (v_isShared_3344_ == 0)
{
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_fst_3340_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_snd_3341_);
v___x_3347_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3349_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 1, v___x_3347_);
v___x_3349_ = v___x_3338_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_fst_3336_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v___x_3347_);
v___x_3349_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
return v___x_3350_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3434_, lean_object* v___x_3435_, lean_object* v_as_3436_, lean_object* v_sz_3437_, lean_object* v_i_3438_, lean_object* v_b_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
size_t v_sz_boxed_3445_; size_t v_i_boxed_3446_; lean_object* v_res_3447_; 
v_sz_boxed_3445_ = lean_unbox_usize(v_sz_3437_);
lean_dec(v_sz_3437_);
v_i_boxed_3446_ = lean_unbox_usize(v_i_3438_);
lean_dec(v_i_3438_);
v_res_3447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3434_, v___x_3435_, v_as_3436_, v_sz_boxed_3445_, v_i_boxed_3446_, v_b_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
lean_dec_ref(v_as_3436_);
lean_dec(v___x_3435_);
lean_dec(v___x_3434_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3448_, size_t v_i_3449_, lean_object* v_bs_3450_){
_start:
{
uint8_t v___x_3451_; 
v___x_3451_ = lean_usize_dec_lt(v_i_3449_, v_sz_3448_);
if (v___x_3451_ == 0)
{
return v_bs_3450_;
}
else
{
lean_object* v_v_3452_; lean_object* v_fst_3453_; lean_object* v_snd_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3470_; 
v_v_3452_ = lean_array_uget(v_bs_3450_, v_i_3449_);
v_fst_3453_ = lean_ctor_get(v_v_3452_, 0);
v_snd_3454_ = lean_ctor_get(v_v_3452_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_v_3452_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3456_ = v_v_3452_;
v_isShared_3457_ = v_isSharedCheck_3470_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_snd_3454_);
lean_inc(v_fst_3453_);
lean_dec(v_v_3452_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3470_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v_bs_x27_3459_; uint8_t v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3463_; 
v___x_3458_ = lean_unsigned_to_nat(0u);
v_bs_x27_3459_ = lean_array_uset(v_bs_3450_, v_i_3449_, v___x_3458_);
v___x_3460_ = 0;
v___x_3461_ = lean_box(v___x_3460_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3461_);
v___x_3463_ = v___x_3456_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3461_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_snd_3454_);
v___x_3463_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3464_; size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_fst_3453_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
v___x_3465_ = ((size_t)1ULL);
v___x_3466_ = lean_usize_add(v_i_3449_, v___x_3465_);
v___x_3467_ = lean_array_uset(v_bs_x27_3459_, v_i_3449_, v___x_3464_);
v_i_3449_ = v___x_3466_;
v_bs_3450_ = v___x_3467_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3471_, lean_object* v_i_3472_, lean_object* v_bs_3473_){
_start:
{
size_t v_sz_boxed_3474_; size_t v_i_boxed_3475_; lean_object* v_res_3476_; 
v_sz_boxed_3474_ = lean_unbox_usize(v_sz_3471_);
lean_dec(v_sz_3471_);
v_i_boxed_3475_ = lean_unbox_usize(v_i_3472_);
lean_dec(v_i_3472_);
v_res_3476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3474_, v_i_boxed_3475_, v_bs_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3477_, lean_object* v___x_3478_, lean_object* v_a_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v___x_30396__overap_3485_; lean_object* v___x_3486_; 
v___x_30396__overap_3485_ = l_instInhabitedOfMonad___redArg(v___x_3477_, v___x_3478_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
v___x_3486_ = lean_apply_5(v___x_30396__overap_3485_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, lean_box(0));
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3487_, lean_object* v___x_3488_, lean_object* v_a_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3487_, v___x_3488_, v_a_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec_ref(v_a_3489_);
return v_res_3495_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_instMonadEIO___redArg();
return v___x_3496_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3498_ = l_StateRefT_x27_instMonad___redArg(v___x_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3503_, lean_object* v_declInfos_3504_, lean_object* v_k_3505_, lean_object* v_kind_3506_, lean_object* v_b_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
uint8_t v_kind_boxed_3513_; lean_object* v_res_3514_; 
v_kind_boxed_3513_ = lean_unbox(v_kind_3506_);
v_res_3514_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3503_, v_declInfos_3504_, v_k_3505_, v_kind_boxed_3513_, v_b_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3515_, lean_object* v_declInfos_3516_, lean_object* v_k_3517_, uint8_t v_kind_3518_, lean_object* v_name_3519_, uint8_t v_bi_3520_, lean_object* v_type_3521_, uint8_t v_kind_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; lean_object* v___f_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_box(v_kind_3518_);
v___f_3529_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3529_, 0, v_acc_3515_);
lean_closure_set(v___f_3529_, 1, v_declInfos_3516_);
lean_closure_set(v___f_3529_, 2, v_k_3517_);
lean_closure_set(v___f_3529_, 3, v___x_3528_);
v___x_3530_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3519_, v_bi_3520_, v_type_3521_, v___f_3529_, v_kind_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v_a_3539_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3530_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3530_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3547_, lean_object* v_k_3548_, uint8_t v_kind_3549_, lean_object* v_acc_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; lean_object* v_toApplicative_3557_; lean_object* v_toFunctor_3558_; lean_object* v_toSeq_3559_; lean_object* v_toSeqLeft_3560_; lean_object* v_toSeqRight_3561_; lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___f_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; lean_object* v___f_3567_; lean_object* v___f_3568_; lean_object* v___f_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v_toApplicative_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3629_; 
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3557_ = lean_ctor_get(v___x_3556_, 0);
v_toFunctor_3558_ = lean_ctor_get(v_toApplicative_3557_, 0);
v_toSeq_3559_ = lean_ctor_get(v_toApplicative_3557_, 2);
v_toSeqLeft_3560_ = lean_ctor_get(v_toApplicative_3557_, 3);
v_toSeqRight_3561_ = lean_ctor_get(v_toApplicative_3557_, 4);
v___f_3562_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3563_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3558_, 2);
v___f_3564_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3564_, 0, v_toFunctor_3558_);
v___f_3565_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3565_, 0, v_toFunctor_3558_);
v___x_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___f_3564_);
lean_ctor_set(v___x_3566_, 1, v___f_3565_);
lean_inc(v_toSeqRight_3561_);
v___f_3567_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3567_, 0, v_toSeqRight_3561_);
lean_inc(v_toSeqLeft_3560_);
v___f_3568_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3568_, 0, v_toSeqLeft_3560_);
lean_inc(v_toSeq_3559_);
v___f_3569_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3569_, 0, v_toSeq_3559_);
v___x_3570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3566_);
lean_ctor_set(v___x_3570_, 1, v___f_3562_);
lean_ctor_set(v___x_3570_, 2, v___f_3569_);
lean_ctor_set(v___x_3570_, 3, v___f_3568_);
lean_ctor_set(v___x_3570_, 4, v___f_3567_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
lean_ctor_set(v___x_3571_, 1, v___f_3563_);
v___x_3572_ = l_StateRefT_x27_instMonad___redArg(v___x_3571_);
v_toApplicative_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v___x_3572_, 1);
lean_dec(v_unused_3630_);
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3629_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_toApplicative_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3629_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_toFunctor_3577_; lean_object* v_toSeq_3578_; lean_object* v_toSeqLeft_3579_; lean_object* v_toSeqRight_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3627_; 
v_toFunctor_3577_ = lean_ctor_get(v_toApplicative_3573_, 0);
v_toSeq_3578_ = lean_ctor_get(v_toApplicative_3573_, 2);
v_toSeqLeft_3579_ = lean_ctor_get(v_toApplicative_3573_, 3);
v_toSeqRight_3580_ = lean_ctor_get(v_toApplicative_3573_, 4);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_toApplicative_3573_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v_toApplicative_3573_, 1);
lean_dec(v_unused_3628_);
v___x_3582_ = v_toApplicative_3573_;
v_isShared_3583_ = v_isSharedCheck_3627_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_toSeqRight_3580_);
lean_inc(v_toSeqLeft_3579_);
lean_inc(v_toSeq_3578_);
lean_inc(v_toFunctor_3577_);
lean_dec(v_toApplicative_3573_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3627_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___x_3593_; 
v___f_3584_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3585_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3577_);
v___f_3586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3586_, 0, v_toFunctor_3577_);
v___f_3587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3587_, 0, v_toFunctor_3577_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___f_3586_);
lean_ctor_set(v___x_3588_, 1, v___f_3587_);
v___f_3589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3589_, 0, v_toSeqRight_3580_);
v___f_3590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3590_, 0, v_toSeqLeft_3579_);
v___f_3591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3591_, 0, v_toSeq_3578_);
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 4, v___f_3589_);
lean_ctor_set(v___x_3582_, 3, v___f_3590_);
lean_ctor_set(v___x_3582_, 2, v___f_3591_);
lean_ctor_set(v___x_3582_, 1, v___f_3584_);
lean_ctor_set(v___x_3582_, 0, v___x_3588_);
v___x_3593_ = v___x_3582_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3588_);
lean_ctor_set(v_reuseFailAlloc_3626_, 1, v___f_3584_);
lean_ctor_set(v_reuseFailAlloc_3626_, 2, v___f_3591_);
lean_ctor_set(v_reuseFailAlloc_3626_, 3, v___f_3590_);
lean_ctor_set(v_reuseFailAlloc_3626_, 4, v___f_3589_);
v___x_3593_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3595_; 
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 1, v___f_3585_);
lean_ctor_set(v___x_3575_, 0, v___x_3593_);
v___x_3595_ = v___x_3575_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___f_3585_);
v___x_3595_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; uint8_t v___x_3598_; 
v___x_3596_ = lean_array_get_size(v_acc_3550_);
v___x_3597_ = lean_array_get_size(v_declInfos_3547_);
v___x_3598_ = lean_nat_dec_lt(v___x_3596_, v___x_3597_);
if (v___x_3598_ == 0)
{
lean_object* v___x_3599_; 
lean_dec_ref(v___x_3595_);
lean_dec_ref(v_declInfos_3547_);
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3553_);
lean_inc(v___y_3552_);
lean_inc_ref(v___y_3551_);
v___x_3599_ = lean_apply_6(v_k_3548_, v_acc_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, lean_box(0));
return v___x_3599_;
}
else
{
lean_object* v___x_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v_snd_3609_; lean_object* v_fst_3610_; lean_object* v_fst_3611_; lean_object* v_snd_3612_; lean_object* v___x_3613_; 
v___x_3600_ = lean_box(0);
v___x_3601_ = 0;
v___x_3602_ = l_Lean_instInhabitedExpr;
v___f_3603_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3603_, 0, v___x_3595_);
lean_closure_set(v___f_3603_, 1, v___x_3602_);
v___f_3604_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3604_, 0, v___f_3603_);
v___x_3605_ = lean_box(v___x_3601_);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___f_3604_);
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3600_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_array_get(v___x_3607_, v_declInfos_3547_, v___x_3596_);
lean_dec_ref_known(v___x_3607_, 2);
v_snd_3609_ = lean_ctor_get(v___x_3608_, 1);
lean_inc(v_snd_3609_);
v_fst_3610_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_fst_3610_);
lean_dec(v___x_3608_);
v_fst_3611_ = lean_ctor_get(v_snd_3609_, 0);
lean_inc(v_fst_3611_);
v_snd_3612_ = lean_ctor_get(v_snd_3609_, 1);
lean_inc(v_snd_3612_);
lean_dec(v_snd_3609_);
lean_inc(v___y_3554_);
lean_inc_ref(v___y_3553_);
lean_inc(v___y_3552_);
lean_inc_ref(v___y_3551_);
lean_inc_ref(v_acc_3550_);
v___x_3613_ = lean_apply_6(v_snd_3612_, v_acc_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, lean_box(0));
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = lean_unbox(v_fst_3611_);
lean_dec(v_fst_3611_);
v___x_3616_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3550_, v_declInfos_3547_, v_k_3548_, v_kind_3549_, v_fst_3610_, v___x_3615_, v_a_3614_, v_kind_3549_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3616_;
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_fst_3611_);
lean_dec(v_fst_3610_);
lean_dec_ref(v_acc_3550_);
lean_dec_ref(v_k_3548_);
lean_dec_ref(v_declInfos_3547_);
v_a_3617_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3613_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3613_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3631_, lean_object* v_declInfos_3632_, lean_object* v_k_3633_, uint8_t v_kind_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_array_push(v_acc_3631_, v_b_3635_);
v___x_3642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3632_, v_k_3633_, v_kind_3634_, v___x_3641_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3643_, lean_object* v_declInfos_3644_, lean_object* v_k_3645_, lean_object* v_kind_3646_, lean_object* v_name_3647_, lean_object* v_bi_3648_, lean_object* v_type_3649_, lean_object* v_kind_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_kind_boxed_3656_; uint8_t v_bi_boxed_3657_; uint8_t v_kind_boxed_3658_; lean_object* v_res_3659_; 
v_kind_boxed_3656_ = lean_unbox(v_kind_3646_);
v_bi_boxed_3657_ = lean_unbox(v_bi_3648_);
v_kind_boxed_3658_ = lean_unbox(v_kind_3650_);
v_res_3659_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3643_, v_declInfos_3644_, v_k_3645_, v_kind_boxed_3656_, v_name_3647_, v_bi_boxed_3657_, v_type_3649_, v_kind_boxed_3658_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3660_, lean_object* v_k_3661_, lean_object* v_kind_3662_, lean_object* v_acc_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
uint8_t v_kind_boxed_3669_; lean_object* v_res_3670_; 
v_kind_boxed_3669_ = lean_unbox(v_kind_3662_);
v_res_3670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3660_, v_k_3661_, v_kind_boxed_3669_, v_acc_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3671_, lean_object* v_k_3672_, uint8_t v_kind_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3680_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3671_, v_k_3672_, v_kind_3673_, v___x_3679_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3681_, lean_object* v_k_3682_, lean_object* v_kind_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_kind_boxed_3689_; lean_object* v_res_3690_; 
v_kind_boxed_3689_ = lean_unbox(v_kind_3683_);
v_res_3690_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3681_, v_k_3682_, v_kind_boxed_3689_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3691_, lean_object* v_k_3692_, uint8_t v_kind_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
size_t v_sz_3699_; size_t v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_sz_3699_ = lean_array_size(v_declInfos_3691_);
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3699_, v___x_3700_, v_declInfos_3691_);
v___x_3702_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3701_, v_k_3692_, v_kind_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3703_, lean_object* v_k_3704_, lean_object* v_kind_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
uint8_t v_kind_boxed_3711_; lean_object* v_res_3712_; 
v_kind_boxed_3711_ = lean_unbox(v_kind_3705_);
v_res_3712_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3703_, v_k_3704_, v_kind_boxed_3711_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
return v_res_3712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3714_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3715_ = lean_unsigned_to_nat(4u);
v___x_3716_ = lean_unsigned_to_nat(202u);
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3718_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3719_ = l_mkPanicMessageWithDecl(v___x_3718_, v___x_3717_, v___x_3716_, v___x_3715_, v___x_3714_);
return v___x_3719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3726_ = l_Lean_stringToMessageData(v___x_3725_);
return v___x_3726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3729_ = l_Lean_stringToMessageData(v___x_3728_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3730_, lean_object* v_numMotives_3731_, lean_object* v_numMinors_3732_, lean_object* v___x_3733_, lean_object* v_all_3734_, lean_object* v___x_3735_, lean_object* v___x_3736_, lean_object* v_head_3737_, lean_object* v_tail_3738_, lean_object* v_recName_3739_, lean_object* v_brecOnGoName_3740_, lean_object* v_levelParams_3741_, lean_object* v_brecOnName_3742_, lean_object* v_brecOnEqName_3743_, lean_object* v_type_3744_, lean_object* v_refArgs_3745_, lean_object* v_refBody_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3752_ = lean_nat_add(v_nParams_3730_, v_numMotives_3731_);
v___x_3753_ = lean_nat_add(v___x_3752_, v_numMinors_3732_);
v___x_3754_ = lean_array_get_size(v_refArgs_3745_);
v___x_3755_ = lean_nat_dec_lt(v___x_3753_, v___x_3754_);
if (v___x_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec(v___x_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_refArgs_3745_);
lean_dec_ref(v_type_3744_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3735_);
lean_dec_ref(v_all_3734_);
lean_dec(v___x_3733_);
lean_dec(v_nParams_3730_);
v___x_3756_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3757_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3756_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3757_;
}
else
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3758_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3730_);
lean_inc_ref_n(v_refArgs_3745_, 2);
v___x_3759_ = l_Array_toSubarray___redArg(v_refArgs_3745_, v___x_3758_, v_nParams_3730_);
lean_inc(v___x_3752_);
v___x_3760_ = l_Array_toSubarray___redArg(v_refArgs_3745_, v_nParams_3730_, v___x_3752_);
v___x_3761_ = l_Subarray_copy___redArg(v___x_3760_);
v___x_3762_ = l_Lean_Expr_getAppFn(v_refBody_3746_);
v___x_3763_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3761_, v___x_3762_);
lean_dec_ref(v___x_3762_);
if (lean_obj_tag(v___x_3763_) == 1)
{
lean_object* v_val_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___f_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec_ref(v_type_3744_);
v_val_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_val_3764_);
lean_dec_ref_known(v___x_3763_, 1);
lean_inc_n(v___x_3753_, 2);
lean_inc_ref_n(v_refArgs_3745_, 2);
v___x_3765_ = l_Array_toSubarray___redArg(v_refArgs_3745_, v___x_3752_, v___x_3753_);
v___x_3766_ = l_Subarray_copy___redArg(v___x_3759_);
v___x_3767_ = l_Subarray_copy___redArg(v___x_3765_);
v___x_3768_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3761_);
lean_inc_ref(v___x_3766_);
lean_inc(v___x_3733_);
v___f_3769_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3769_, 0, v___x_3733_);
lean_closure_set(v___f_3769_, 1, v___x_3766_);
lean_closure_set(v___f_3769_, 2, v___x_3761_);
lean_closure_set(v___f_3769_, 3, v_all_3734_);
lean_closure_set(v___f_3769_, 4, v___x_3735_);
lean_closure_set(v___f_3769_, 5, v___x_3758_);
lean_closure_set(v___f_3769_, 6, v___x_3768_);
v___x_3770_ = lean_nat_sub(v___x_3754_, v___x_3768_);
lean_inc(v___x_3770_);
v___x_3771_ = l_Array_toSubarray___redArg(v_refArgs_3745_, v___x_3753_, v___x_3770_);
v___x_3772_ = l_Subarray_copy___redArg(v___x_3771_);
v___x_3773_ = lean_array_get(v___x_3736_, v_refArgs_3745_, v___x_3770_);
lean_dec(v___x_3770_);
lean_dec_ref(v_refArgs_3745_);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v___y_3747_);
lean_inc(v___x_3773_);
v___x_3774_ = lean_infer_type(v___x_3773_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3776_; 
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref_known(v___x_3774_, 1);
lean_inc(v___y_3750_);
lean_inc_ref(v___y_3749_);
lean_inc(v___y_3748_);
lean_inc_ref(v___y_3747_);
v___x_3776_ = lean_infer_type(v_a_3775_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3778_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v___x_3778_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3777_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_a_3779_);
lean_dec_ref_known(v___x_3778_, 1);
if (lean_obj_tag(v_a_3779_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___f_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; size_t v_sz_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v_val_3780_ = lean_ctor_get(v_a_3779_, 0);
lean_inc(v_val_3780_);
lean_dec_ref_known(v_a_3779_, 1);
v___x_3781_ = l_Lean_mkLevelMax(v_val_3780_, v_head_3737_);
v___x_3782_ = lean_array_get_size(v___x_3761_);
v___x_3783_ = l_Array_ofFn___redArg(v___x_3782_, v___f_3769_);
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3785_ = lean_array_get_size(v___x_3783_);
lean_inc_ref(v___x_3783_);
v___x_3786_ = l_Array_toSubarray___redArg(v___x_3783_, v___x_3758_, v___x_3785_);
v___x_3787_ = lean_box(v___x_3755_);
lean_inc(v___x_3753_);
lean_inc_ref(v___x_3761_);
lean_inc_ref(v___x_3786_);
v___f_3788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3788_, 0, v___x_3781_);
lean_closure_set(v___f_3788_, 1, v_tail_3738_);
lean_closure_set(v___f_3788_, 2, v_recName_3739_);
lean_closure_set(v___f_3788_, 3, v___x_3766_);
lean_closure_set(v___f_3788_, 4, v___x_3786_);
lean_closure_set(v___f_3788_, 5, v___x_3761_);
lean_closure_set(v___f_3788_, 6, v___x_3753_);
lean_closure_set(v___f_3788_, 7, v___x_3754_);
lean_closure_set(v___f_3788_, 8, v___x_3767_);
lean_closure_set(v___f_3788_, 9, v___x_3783_);
lean_closure_set(v___f_3788_, 10, v___x_3772_);
lean_closure_set(v___f_3788_, 11, v___x_3773_);
lean_closure_set(v___f_3788_, 12, v___x_3768_);
lean_closure_set(v___f_3788_, 13, v___x_3736_);
lean_closure_set(v___f_3788_, 14, v_val_3764_);
lean_closure_set(v___f_3788_, 15, v___x_3787_);
lean_closure_set(v___f_3788_, 16, v_brecOnGoName_3740_);
lean_closure_set(v___f_3788_, 17, v_levelParams_3741_);
lean_closure_set(v___f_3788_, 18, v___x_3733_);
lean_closure_set(v___f_3788_, 19, v_brecOnName_3742_);
lean_closure_set(v___f_3788_, 20, v___x_3758_);
lean_closure_set(v___f_3788_, 21, v_brecOnEqName_3743_);
v___x_3789_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
lean_ctor_set(v___x_3790_, 1, v___x_3782_);
v___x_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3786_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3784_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v_sz_3793_ = lean_array_size(v___x_3761_);
v___x_3794_ = ((size_t)0ULL);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3753_, v___x_3754_, v___x_3761_, v_sz_3793_, v___x_3794_, v___x_3792_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3753_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v_fst_3797_; uint8_t v___x_3798_; lean_object* v___x_3799_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v_fst_3797_ = lean_ctor_get(v_a_3796_, 0);
lean_inc(v_fst_3797_);
lean_dec(v_a_3796_);
v___x_3798_ = 0;
v___x_3799_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3797_, v___f_3788_, v___x_3798_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3799_;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v___f_3788_);
v_a_3800_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3795_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3795_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_dec(v_a_3779_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v___x_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v_val_3764_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3753_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3733_);
v___x_3808_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3809_ = l_Lean_MessageData_ofExpr(v___x_3773_);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3812_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3813_;
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v___x_3773_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v___x_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v_val_3764_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3753_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3733_);
v_a_3814_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3778_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3778_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec(v___x_3773_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v___x_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v_val_3764_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3753_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3733_);
v_a_3822_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3776_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3776_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v___x_3773_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___f_3769_);
lean_dec_ref(v___x_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v_val_3764_);
lean_dec_ref(v___x_3761_);
lean_dec(v___x_3753_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3733_);
v_a_3830_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3774_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3774_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_dec(v___x_3763_);
lean_dec_ref(v___x_3759_);
lean_dec(v___x_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_refArgs_3745_);
lean_dec(v_brecOnEqName_3743_);
lean_dec(v_brecOnName_3742_);
lean_dec(v_levelParams_3741_);
lean_dec(v_brecOnGoName_3740_);
lean_dec(v_recName_3739_);
lean_dec(v_tail_3738_);
lean_dec(v_head_3737_);
lean_dec_ref(v___x_3736_);
lean_dec(v___x_3735_);
lean_dec_ref(v_all_3734_);
lean_dec(v___x_3733_);
v___x_3838_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3839_ = l_Lean_MessageData_ofExpr(v_type_3744_);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_array_to_list(v___x_3761_);
v___x_3844_ = lean_box(0);
v___x_3845_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3843_, v___x_3844_);
v___x_3846_ = l_Lean_MessageData_ofList(v___x_3845_);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3842_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3847_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3849_ = _args[0];
lean_object* v_numMotives_3850_ = _args[1];
lean_object* v_numMinors_3851_ = _args[2];
lean_object* v___x_3852_ = _args[3];
lean_object* v_all_3853_ = _args[4];
lean_object* v___x_3854_ = _args[5];
lean_object* v___x_3855_ = _args[6];
lean_object* v_head_3856_ = _args[7];
lean_object* v_tail_3857_ = _args[8];
lean_object* v_recName_3858_ = _args[9];
lean_object* v_brecOnGoName_3859_ = _args[10];
lean_object* v_levelParams_3860_ = _args[11];
lean_object* v_brecOnName_3861_ = _args[12];
lean_object* v_brecOnEqName_3862_ = _args[13];
lean_object* v_type_3863_ = _args[14];
lean_object* v_refArgs_3864_ = _args[15];
lean_object* v_refBody_3865_ = _args[16];
lean_object* v___y_3866_ = _args[17];
lean_object* v___y_3867_ = _args[18];
lean_object* v___y_3868_ = _args[19];
lean_object* v___y_3869_ = _args[20];
lean_object* v___y_3870_ = _args[21];
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3849_, v_numMotives_3850_, v_numMinors_3851_, v___x_3852_, v_all_3853_, v___x_3854_, v___x_3855_, v_head_3856_, v_tail_3857_, v_recName_3858_, v_brecOnGoName_3859_, v_levelParams_3860_, v_brecOnName_3861_, v_brecOnEqName_3862_, v_type_3863_, v_refArgs_3864_, v_refBody_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec_ref(v_refBody_3865_);
lean_dec(v_numMinors_3851_);
lean_dec(v_numMotives_3850_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3874_, lean_object* v_nParams_3875_, lean_object* v_all_3876_, lean_object* v_brecOnName_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v_brecOnGoName_3886_; lean_object* v___x_3887_; lean_object* v_brecOnEqName_3888_; lean_object* v___x_3889_; 
v___x_3883_ = l_Lean_instInhabitedExpr;
v___x_3884_ = lean_box(0);
v___x_3885_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3877_, 2);
v_brecOnGoName_3886_ = l_Lean_Name_str___override(v_brecOnName_3877_, v___x_3885_);
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3888_ = l_Lean_Name_str___override(v_brecOnName_3877_, v___x_3887_);
lean_inc(v_recName_3874_);
v___x_3889_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3874_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3917_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3892_ = v___x_3889_;
v_isShared_3893_ = v_isSharedCheck_3917_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_a_3890_);
lean_dec(v___x_3889_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3917_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
if (lean_obj_tag(v_a_3890_) == 7)
{
lean_object* v_val_3894_; lean_object* v_toConstantVal_3895_; lean_object* v_numMotives_3896_; lean_object* v_numMinors_3897_; lean_object* v_levelParams_3898_; lean_object* v_type_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_del_object(v___x_3892_);
v_val_3894_ = lean_ctor_get(v_a_3890_, 0);
lean_inc_ref(v_val_3894_);
lean_dec_ref_known(v_a_3890_, 1);
v_toConstantVal_3895_ = lean_ctor_get(v_val_3894_, 0);
lean_inc_ref(v_toConstantVal_3895_);
v_numMotives_3896_ = lean_ctor_get(v_val_3894_, 4);
lean_inc(v_numMotives_3896_);
v_numMinors_3897_ = lean_ctor_get(v_val_3894_, 5);
lean_inc(v_numMinors_3897_);
lean_dec_ref(v_val_3894_);
v_levelParams_3898_ = lean_ctor_get(v_toConstantVal_3895_, 1);
lean_inc_n(v_levelParams_3898_, 2);
v_type_3899_ = lean_ctor_get(v_toConstantVal_3895_, 2);
lean_inc_ref(v_type_3899_);
lean_dec_ref(v_toConstantVal_3895_);
v___x_3900_ = lean_box(0);
v___x_3901_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3898_, v___x_3900_);
if (lean_obj_tag(v___x_3901_) == 1)
{
lean_object* v_head_3902_; lean_object* v_tail_3903_; lean_object* v___f_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
v_head_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_head_3902_);
v_tail_3903_ = lean_ctor_get(v___x_3901_, 1);
lean_inc(v_tail_3903_);
lean_inc_ref(v_type_3899_);
v___f_3904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3904_, 0, v_nParams_3875_);
lean_closure_set(v___f_3904_, 1, v_numMotives_3896_);
lean_closure_set(v___f_3904_, 2, v_numMinors_3897_);
lean_closure_set(v___f_3904_, 3, v___x_3901_);
lean_closure_set(v___f_3904_, 4, v_all_3876_);
lean_closure_set(v___f_3904_, 5, v___x_3884_);
lean_closure_set(v___f_3904_, 6, v___x_3883_);
lean_closure_set(v___f_3904_, 7, v_head_3902_);
lean_closure_set(v___f_3904_, 8, v_tail_3903_);
lean_closure_set(v___f_3904_, 9, v_recName_3874_);
lean_closure_set(v___f_3904_, 10, v_brecOnGoName_3886_);
lean_closure_set(v___f_3904_, 11, v_levelParams_3898_);
lean_closure_set(v___f_3904_, 12, v_brecOnName_3877_);
lean_closure_set(v___f_3904_, 13, v_brecOnEqName_3888_);
lean_closure_set(v___f_3904_, 14, v_type_3899_);
v___x_3905_ = 0;
v___x_3906_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3899_, v___f_3904_, v___x_3905_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
return v___x_3906_;
}
else
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
lean_dec(v___x_3901_);
lean_dec_ref(v_type_3899_);
lean_dec(v_levelParams_3898_);
lean_dec(v_numMinors_3897_);
lean_dec(v_numMotives_3896_);
lean_dec(v_brecOnEqName_3888_);
lean_dec(v_brecOnGoName_3886_);
lean_dec(v_brecOnName_3877_);
lean_dec_ref(v_all_3876_);
lean_dec(v_nParams_3875_);
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3908_ = l_Lean_MessageData_ofName(v_recName_3874_);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
v___x_3912_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3911_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
return v___x_3912_;
}
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_a_3890_);
lean_dec(v_brecOnEqName_3888_);
lean_dec(v_brecOnGoName_3886_);
lean_dec(v_brecOnName_3877_);
lean_dec_ref(v_all_3876_);
lean_dec(v_nParams_3875_);
lean_dec(v_recName_3874_);
v___x_3913_ = lean_box(0);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 0, v___x_3913_);
v___x_3915_ = v___x_3892_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec(v_brecOnEqName_3888_);
lean_dec(v_brecOnGoName_3886_);
lean_dec(v_brecOnName_3877_);
lean_dec_ref(v_all_3876_);
lean_dec(v_nParams_3875_);
lean_dec(v_recName_3874_);
v_a_3918_ = lean_ctor_get(v___x_3889_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3889_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3889_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3889_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3926_, lean_object* v_nParams_3927_, lean_object* v_all_3928_, lean_object* v_brecOnName_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3926_, v_nParams_3927_, v_all_3928_, v_brecOnName_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v___x_3939_, lean_object* v___x_3940_, lean_object* v_a_3941_, lean_object* v_b_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_nat_dec_lt(v_a_3941_, v_upperBound_3936_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec(v_a_3941_);
lean_dec_ref(v___x_3940_);
lean_dec(v___x_3939_);
lean_dec(v___x_3938_);
lean_dec(v___x_3937_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3942_);
return v___x_3949_;
}
else
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3950_ = lean_box(0);
v___x_3951_ = lean_unsigned_to_nat(1u);
v___x_3952_ = lean_nat_add(v_a_3941_, v___x_3951_);
lean_dec(v_a_3941_);
lean_inc_n(v___x_3952_, 2);
lean_inc(v___x_3937_);
v___x_3953_ = lean_name_append_index_after(v___x_3937_, v___x_3952_);
lean_inc(v___x_3938_);
v___x_3954_ = lean_name_append_index_after(v___x_3938_, v___x_3952_);
lean_inc_ref(v___x_3940_);
lean_inc(v___x_3939_);
v___x_3955_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3953_, v___x_3939_, v___x_3940_, v___x_3954_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_dec_ref_known(v___x_3955_, 1);
v_a_3941_ = v___x_3952_;
v_b_3942_ = v___x_3950_;
goto _start;
}
else
{
lean_dec(v___x_3952_);
lean_dec_ref(v___x_3940_);
lean_dec(v___x_3939_);
lean_dec(v___x_3938_);
lean_dec(v___x_3937_);
return v___x_3955_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3957_, lean_object* v___x_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v_a_3962_, lean_object* v_b_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3957_, v___x_3958_, v___x_3959_, v___x_3960_, v___x_3961_, v_a_3962_, v_b_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v_upperBound_3957_);
return v_res_3969_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3975_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3976_ = l_Lean_Name_append(v___x_3975_, v___x_3974_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_toCold_3983_; lean_object* v_options_3984_; lean_object* v_inheritedTraceOptions_3985_; uint8_t v_hasTrace_3986_; lean_object* v___x_3987_; 
v_toCold_3983_ = lean_ctor_get(v_a_3980_, 0);
v_options_3984_ = lean_ctor_get(v_toCold_3983_, 2);
v_inheritedTraceOptions_3985_ = lean_ctor_get(v_toCold_3983_, 11);
v_hasTrace_3986_ = lean_ctor_get_uint8(v_options_3984_, sizeof(void*)*1);
v___x_3987_ = lean_box(0);
if (v_hasTrace_3986_ == 0)
{
lean_object* v___x_3988_; 
lean_inc(v_indName_3977_);
v___x_3988_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4053_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_3991_ = v___x_3988_;
v_isShared_3992_ = v_isSharedCheck_4053_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3988_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4053_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
if (lean_obj_tag(v_a_3989_) == 5)
{
lean_object* v_val_3993_; uint8_t v_isRec_3994_; 
v_val_3993_ = lean_ctor_get(v_a_3989_, 0);
lean_inc_ref(v_val_3993_);
lean_dec_ref_known(v_a_3989_, 1);
v_isRec_3994_ = lean_ctor_get_uint8(v_val_3993_, sizeof(void*)*6);
if (v_isRec_3994_ == 0)
{
lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec_ref(v_val_3993_);
lean_dec(v_indName_3977_);
v___x_3995_ = lean_box(0);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v___x_3995_);
v___x_3997_ = v___x_3991_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_object* v_toConstantVal_3999_; lean_object* v_numParams_4000_; lean_object* v_all_4001_; lean_object* v_numNested_4002_; lean_object* v_type_4003_; lean_object* v___x_4004_; 
lean_del_object(v___x_3991_);
v_toConstantVal_3999_ = lean_ctor_get(v_val_3993_, 0);
lean_inc_ref(v_toConstantVal_3999_);
v_numParams_4000_ = lean_ctor_get(v_val_3993_, 1);
lean_inc(v_numParams_4000_);
v_all_4001_ = lean_ctor_get(v_val_3993_, 3);
lean_inc(v_all_4001_);
v_numNested_4002_ = lean_ctor_get(v_val_3993_, 5);
lean_inc(v_numNested_4002_);
lean_dec_ref(v_val_3993_);
v_type_4003_ = lean_ctor_get(v_toConstantVal_3999_, 2);
lean_inc_ref(v_type_4003_);
lean_dec_ref(v_toConstantVal_3999_);
v___x_4004_ = l_Lean_Meta_isPropFormerType(v_type_4003_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4040_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4007_ = v___x_4004_;
v_isShared_4008_ = v_isSharedCheck_4040_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4040_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_unbox(v_a_4005_);
lean_dec(v_a_4005_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_del_object(v___x_4007_);
lean_inc_n(v_indName_3977_, 2);
v___x_4010_ = l_Lean_mkRecName(v_indName_3977_);
v___x_4011_ = l_Lean_mkBRecOnName(v_indName_3977_);
lean_inc(v_all_4001_);
v___x_4012_ = lean_array_mk(v_all_4001_);
lean_inc(v___x_4011_);
lean_inc_ref(v___x_4012_);
lean_inc(v_numParams_4000_);
lean_inc(v___x_4010_);
v___x_4013_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4010_, v_numParams_4000_, v___x_4012_, v___x_4011_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4034_; 
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4034_ == 0)
{
lean_object* v_unused_4035_; 
v_unused_4035_ = lean_ctor_get(v___x_4013_, 0);
lean_dec(v_unused_4035_);
v___x_4015_ = v___x_4013_;
v_isShared_4016_ = v_isSharedCheck_4034_;
goto v_resetjp_4014_;
}
else
{
lean_dec(v___x_4013_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4034_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = l_List_get_x21Internal___redArg(v___x_3987_, v_all_4001_, v___x_4017_);
lean_dec(v_all_4001_);
v___x_4019_ = lean_name_eq(v___x_4018_, v_indName_3977_);
lean_dec(v_indName_3977_);
lean_dec(v___x_4018_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4022_; 
lean_dec_ref(v___x_4012_);
lean_dec(v___x_4011_);
lean_dec(v___x_4010_);
lean_dec(v_numNested_4002_);
lean_dec(v_numParams_4000_);
v___x_4020_ = lean_box(0);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4020_);
v___x_4022_ = v___x_4015_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___x_4020_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
lean_del_object(v___x_4015_);
v___x_4024_ = lean_box(0);
v___x_4025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4002_, v___x_4010_, v___x_4011_, v_numParams_4000_, v___x_4012_, v___x_4017_, v___x_4024_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
lean_dec(v_numNested_4002_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v___x_4025_, 0);
lean_dec(v_unused_4033_);
v___x_4027_ = v___x_4025_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_dec(v___x_4025_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4024_);
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4024_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
else
{
return v___x_4025_;
}
}
}
}
else
{
lean_dec_ref(v___x_4012_);
lean_dec(v___x_4011_);
lean_dec(v___x_4010_);
lean_dec(v_numNested_4002_);
lean_dec(v_all_4001_);
lean_dec(v_numParams_4000_);
lean_dec(v_indName_3977_);
return v___x_4013_;
}
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4038_; 
lean_dec(v_numNested_4002_);
lean_dec(v_all_4001_);
lean_dec(v_numParams_4000_);
lean_dec(v_indName_3977_);
v___x_4036_ = lean_box(0);
if (v_isShared_4008_ == 0)
{
lean_ctor_set(v___x_4007_, 0, v___x_4036_);
v___x_4038_ = v___x_4007_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v_numNested_4002_);
lean_dec(v_all_4001_);
lean_dec(v_numParams_4000_);
lean_dec(v_indName_3977_);
v_a_4041_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4004_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4004_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
lean_dec(v_a_3989_);
lean_dec(v_indName_3977_);
v___x_4049_ = lean_box(0);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 0, v___x_4049_);
v___x_4051_ = v___x_3991_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_indName_3977_);
v_a_4054_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_3988_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_3988_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v___f_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v_a_4070_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v_a_4085_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v_a_4090_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v_a_4095_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v_a_4107_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v_a_4112_; 
lean_inc(v_indName_3977_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4062_, 0, v_indName_3977_);
v___x_4063_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4064_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4065_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3985_, v_options_3984_, v___x_4065_);
if (v___x_4066_ == 0)
{
lean_object* v___x_4179_; uint8_t v___x_4180_; 
v___x_4179_ = l_Lean_trace_profiler;
v___x_4180_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3984_, v___x_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
lean_dec_ref(v___f_4062_);
lean_inc(v_indName_3977_);
v___x_4181_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4246_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4184_ = v___x_4181_;
v_isShared_4185_ = v_isSharedCheck_4246_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4181_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4246_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
if (lean_obj_tag(v_a_4182_) == 5)
{
lean_object* v_val_4186_; uint8_t v_isRec_4187_; 
v_val_4186_ = lean_ctor_get(v_a_4182_, 0);
lean_inc_ref(v_val_4186_);
lean_dec_ref_known(v_a_4182_, 1);
v_isRec_4187_ = lean_ctor_get_uint8(v_val_4186_, sizeof(void*)*6);
if (v_isRec_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
lean_dec_ref(v_val_4186_);
lean_dec(v_indName_3977_);
v___x_4188_ = lean_box(0);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v___x_4188_);
v___x_4190_ = v___x_4184_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
else
{
lean_object* v_toConstantVal_4192_; lean_object* v_numParams_4193_; lean_object* v_all_4194_; lean_object* v_numNested_4195_; lean_object* v_type_4196_; lean_object* v___x_4197_; 
lean_del_object(v___x_4184_);
v_toConstantVal_4192_ = lean_ctor_get(v_val_4186_, 0);
lean_inc_ref(v_toConstantVal_4192_);
v_numParams_4193_ = lean_ctor_get(v_val_4186_, 1);
lean_inc(v_numParams_4193_);
v_all_4194_ = lean_ctor_get(v_val_4186_, 3);
lean_inc(v_all_4194_);
v_numNested_4195_ = lean_ctor_get(v_val_4186_, 5);
lean_inc(v_numNested_4195_);
lean_dec_ref(v_val_4186_);
v_type_4196_ = lean_ctor_get(v_toConstantVal_4192_, 2);
lean_inc_ref(v_type_4196_);
lean_dec_ref(v_toConstantVal_4192_);
v___x_4197_ = l_Lean_Meta_isPropFormerType(v_type_4196_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4233_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4233_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4233_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
uint8_t v___x_4202_; 
v___x_4202_ = lean_unbox(v_a_4198_);
lean_dec(v_a_4198_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_del_object(v___x_4200_);
lean_inc_n(v_indName_3977_, 2);
v___x_4203_ = l_Lean_mkRecName(v_indName_3977_);
v___x_4204_ = l_Lean_mkBRecOnName(v_indName_3977_);
lean_inc(v_all_4194_);
v___x_4205_ = lean_array_mk(v_all_4194_);
lean_inc(v___x_4204_);
lean_inc_ref(v___x_4205_);
lean_inc(v_numParams_4193_);
lean_inc(v___x_4203_);
v___x_4206_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4203_, v_numParams_4193_, v___x_4205_, v___x_4204_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4227_; 
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4227_ == 0)
{
lean_object* v_unused_4228_; 
v_unused_4228_ = lean_ctor_get(v___x_4206_, 0);
lean_dec(v_unused_4228_);
v___x_4208_ = v___x_4206_;
v_isShared_4209_ = v_isSharedCheck_4227_;
goto v_resetjp_4207_;
}
else
{
lean_dec(v___x_4206_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4227_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4210_ = lean_unsigned_to_nat(0u);
v___x_4211_ = l_List_get_x21Internal___redArg(v___x_3987_, v_all_4194_, v___x_4210_);
lean_dec(v_all_4194_);
v___x_4212_ = lean_name_eq(v___x_4211_, v_indName_3977_);
lean_dec(v_indName_3977_);
lean_dec(v___x_4211_);
if (v___x_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_dec_ref(v___x_4205_);
lean_dec(v___x_4204_);
lean_dec(v___x_4203_);
lean_dec(v_numNested_4195_);
lean_dec(v_numParams_4193_);
v___x_4213_ = lean_box(0);
if (v_isShared_4209_ == 0)
{
lean_ctor_set(v___x_4208_, 0, v___x_4213_);
v___x_4215_ = v___x_4208_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4218_; 
lean_del_object(v___x_4208_);
v___x_4217_ = lean_box(0);
v___x_4218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4195_, v___x_4203_, v___x_4204_, v_numParams_4193_, v___x_4205_, v___x_4210_, v___x_4217_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
lean_dec(v_numNested_4195_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4225_ == 0)
{
lean_object* v_unused_4226_; 
v_unused_4226_ = lean_ctor_get(v___x_4218_, 0);
lean_dec(v_unused_4226_);
v___x_4220_ = v___x_4218_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_dec(v___x_4218_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
lean_ctor_set(v___x_4220_, 0, v___x_4217_);
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4217_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
else
{
return v___x_4218_;
}
}
}
}
else
{
lean_dec_ref(v___x_4205_);
lean_dec(v___x_4204_);
lean_dec(v___x_4203_);
lean_dec(v_numNested_4195_);
lean_dec(v_all_4194_);
lean_dec(v_numParams_4193_);
lean_dec(v_indName_3977_);
return v___x_4206_;
}
}
else
{
lean_object* v___x_4229_; lean_object* v___x_4231_; 
lean_dec(v_numNested_4195_);
lean_dec(v_all_4194_);
lean_dec(v_numParams_4193_);
lean_dec(v_indName_3977_);
v___x_4229_ = lean_box(0);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4229_);
v___x_4231_ = v___x_4200_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_numNested_4195_);
lean_dec(v_all_4194_);
lean_dec(v_numParams_4193_);
lean_dec(v_indName_3977_);
v_a_4234_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4197_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4197_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
lean_dec(v_a_4182_);
lean_dec(v_indName_3977_);
v___x_4242_ = lean_box(0);
if (v_isShared_4185_ == 0)
{
lean_ctor_set(v___x_4184_, 0, v___x_4242_);
v___x_4244_ = v___x_4184_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4242_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v_indName_3977_);
v_a_4247_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4181_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4181_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
else
{
goto v___jp_4114_;
}
}
else
{
goto v___jp_4114_;
}
v___jp_4067_:
{
lean_object* v___x_4071_; double v___x_4072_; double v___x_4073_; double v___x_4074_; double v___x_4075_; double v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4071_ = lean_io_mono_nanos_now();
v___x_4072_ = lean_float_of_nat(v___y_4069_);
v___x_4073_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4074_ = lean_float_div(v___x_4072_, v___x_4073_);
v___x_4075_ = lean_float_of_nat(v___x_4071_);
v___x_4076_ = lean_float_div(v___x_4075_, v___x_4073_);
v___x_4077_ = lean_box_float(v___x_4074_);
v___x_4078_ = lean_box_float(v___x_4076_);
v___x_4079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4077_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4080_, 0, v_a_4070_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4063_, v_hasTrace_3986_, v___x_4064_, v_options_3984_, v___x_4066_, v___y_4068_, v___f_4062_, v___x_4080_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4081_;
}
v___jp_4082_:
{
lean_object* v___x_4086_; 
v___x_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4086_, 0, v_a_4085_);
v___y_4068_ = v___y_4083_;
v___y_4069_ = v___y_4084_;
v_a_4070_ = v___x_4086_;
goto v___jp_4067_;
}
v___jp_4087_:
{
lean_object* v___x_4091_; 
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_a_4090_);
v___y_4068_ = v___y_4088_;
v___y_4069_ = v___y_4089_;
v_a_4070_ = v___x_4091_;
goto v___jp_4067_;
}
v___jp_4092_:
{
lean_object* v___x_4096_; double v___x_4097_; double v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4096_ = lean_io_get_num_heartbeats();
v___x_4097_ = lean_float_of_nat(v___y_4094_);
v___x_4098_ = lean_float_of_nat(v___x_4096_);
v___x_4099_ = lean_box_float(v___x_4097_);
v___x_4100_ = lean_box_float(v___x_4098_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4099_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4102_, 0, v_a_4095_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
v___x_4103_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4063_, v_hasTrace_3986_, v___x_4064_, v_options_3984_, v___x_4066_, v___y_4093_, v___f_4062_, v___x_4102_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
return v___x_4103_;
}
v___jp_4104_:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_a_4107_);
v___y_4093_ = v___y_4105_;
v___y_4094_ = v___y_4106_;
v_a_4095_ = v___x_4108_;
goto v___jp_4092_;
}
v___jp_4109_:
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_a_4112_);
v___y_4093_ = v___y_4110_;
v___y_4094_ = v___y_4111_;
v_a_4095_ = v___x_4113_;
goto v___jp_4092_;
}
v___jp_4114_:
{
lean_object* v___x_4115_; lean_object* v_a_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; 
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3981_);
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
lean_inc(v_a_4116_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4118_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3984_, v___x_4117_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4119_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3977_);
v___x_4120_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
if (lean_obj_tag(v_a_4121_) == 5)
{
lean_object* v_val_4122_; uint8_t v_isRec_4123_; 
v_val_4122_ = lean_ctor_get(v_a_4121_, 0);
lean_inc_ref(v_val_4122_);
lean_dec_ref_known(v_a_4121_, 1);
v_isRec_4123_ = lean_ctor_get_uint8(v_val_4122_, sizeof(void*)*6);
if (v_isRec_4123_ == 0)
{
lean_object* v___x_4124_; 
lean_dec_ref(v_val_4122_);
lean_dec(v_indName_3977_);
v___x_4124_ = lean_box(0);
v___y_4083_ = v_a_4116_;
v___y_4084_ = v___x_4119_;
v_a_4085_ = v___x_4124_;
goto v___jp_4082_;
}
else
{
lean_object* v_toConstantVal_4125_; lean_object* v_numParams_4126_; lean_object* v_all_4127_; lean_object* v_numNested_4128_; lean_object* v_type_4129_; lean_object* v___x_4130_; 
v_toConstantVal_4125_ = lean_ctor_get(v_val_4122_, 0);
lean_inc_ref(v_toConstantVal_4125_);
v_numParams_4126_ = lean_ctor_get(v_val_4122_, 1);
lean_inc(v_numParams_4126_);
v_all_4127_ = lean_ctor_get(v_val_4122_, 3);
lean_inc(v_all_4127_);
v_numNested_4128_ = lean_ctor_get(v_val_4122_, 5);
lean_inc(v_numNested_4128_);
lean_dec_ref(v_val_4122_);
v_type_4129_ = lean_ctor_get(v_toConstantVal_4125_, 2);
lean_inc_ref(v_type_4129_);
lean_dec_ref(v_toConstantVal_4125_);
v___x_4130_ = l_Lean_Meta_isPropFormerType(v_type_4129_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; uint8_t v___x_4132_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = lean_unbox(v_a_4131_);
lean_dec(v_a_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_inc_n(v_indName_3977_, 2);
v___x_4133_ = l_Lean_mkRecName(v_indName_3977_);
v___x_4134_ = l_Lean_mkBRecOnName(v_indName_3977_);
lean_inc(v_all_4127_);
v___x_4135_ = lean_array_mk(v_all_4127_);
lean_inc(v___x_4134_);
lean_inc_ref(v___x_4135_);
lean_inc(v_numParams_4126_);
lean_inc(v___x_4133_);
v___x_4136_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4133_, v_numParams_4126_, v___x_4135_, v___x_4134_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v___x_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
lean_dec_ref_known(v___x_4136_, 1);
v___x_4137_ = lean_unsigned_to_nat(0u);
v___x_4138_ = l_List_get_x21Internal___redArg(v___x_3987_, v_all_4127_, v___x_4137_);
lean_dec(v_all_4127_);
v___x_4139_ = lean_name_eq(v___x_4138_, v_indName_3977_);
lean_dec(v_indName_3977_);
lean_dec(v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; 
lean_dec_ref(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v___x_4133_);
lean_dec(v_numNested_4128_);
lean_dec(v_numParams_4126_);
v___x_4140_ = lean_box(0);
v___y_4083_ = v_a_4116_;
v___y_4084_ = v___x_4119_;
v_a_4085_ = v___x_4140_;
goto v___jp_4082_;
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4141_ = lean_box(0);
v___x_4142_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4128_, v___x_4133_, v___x_4134_, v_numParams_4126_, v___x_4135_, v___x_4137_, v___x_4141_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
lean_dec(v_numNested_4128_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_dec_ref_known(v___x_4142_, 1);
v___y_4083_ = v_a_4116_;
v___y_4084_ = v___x_4119_;
v_a_4085_ = v___x_4141_;
goto v___jp_4082_;
}
else
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___y_4088_ = v_a_4116_;
v___y_4089_ = v___x_4119_;
v_a_4090_ = v_a_4143_;
goto v___jp_4087_;
}
}
}
else
{
lean_object* v_a_4144_; 
lean_dec_ref(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v___x_4133_);
lean_dec(v_numNested_4128_);
lean_dec(v_all_4127_);
lean_dec(v_numParams_4126_);
lean_dec(v_indName_3977_);
v_a_4144_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4136_, 1);
v___y_4088_ = v_a_4116_;
v___y_4089_ = v___x_4119_;
v_a_4090_ = v_a_4144_;
goto v___jp_4087_;
}
}
else
{
lean_object* v___x_4145_; 
lean_dec(v_numNested_4128_);
lean_dec(v_all_4127_);
lean_dec(v_numParams_4126_);
lean_dec(v_indName_3977_);
v___x_4145_ = lean_box(0);
v___y_4083_ = v_a_4116_;
v___y_4084_ = v___x_4119_;
v_a_4085_ = v___x_4145_;
goto v___jp_4082_;
}
}
else
{
lean_object* v_a_4146_; 
lean_dec(v_numNested_4128_);
lean_dec(v_all_4127_);
lean_dec(v_numParams_4126_);
lean_dec(v_indName_3977_);
v_a_4146_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4130_, 1);
v___y_4088_ = v_a_4116_;
v___y_4089_ = v___x_4119_;
v_a_4090_ = v_a_4146_;
goto v___jp_4087_;
}
}
}
else
{
lean_object* v___x_4147_; 
lean_dec(v_a_4121_);
lean_dec(v_indName_3977_);
v___x_4147_ = lean_box(0);
v___y_4083_ = v_a_4116_;
v___y_4084_ = v___x_4119_;
v_a_4085_ = v___x_4147_;
goto v___jp_4082_;
}
}
else
{
lean_object* v_a_4148_; 
lean_dec(v_indName_3977_);
v_a_4148_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4120_, 1);
v___y_4088_ = v_a_4116_;
v___y_4089_ = v___x_4119_;
v_a_4090_ = v_a_4148_;
goto v___jp_4087_;
}
}
else
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3977_);
v___x_4150_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
if (lean_obj_tag(v_a_4151_) == 5)
{
lean_object* v_val_4152_; uint8_t v_isRec_4153_; 
v_val_4152_ = lean_ctor_get(v_a_4151_, 0);
lean_inc_ref(v_val_4152_);
lean_dec_ref_known(v_a_4151_, 1);
v_isRec_4153_ = lean_ctor_get_uint8(v_val_4152_, sizeof(void*)*6);
if (v_isRec_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec_ref(v_val_4152_);
lean_dec(v_indName_3977_);
v___x_4154_ = lean_box(0);
v___y_4105_ = v_a_4116_;
v___y_4106_ = v___x_4149_;
v_a_4107_ = v___x_4154_;
goto v___jp_4104_;
}
else
{
lean_object* v_toConstantVal_4155_; lean_object* v_numParams_4156_; lean_object* v_all_4157_; lean_object* v_numNested_4158_; lean_object* v_type_4159_; lean_object* v___x_4160_; 
v_toConstantVal_4155_ = lean_ctor_get(v_val_4152_, 0);
lean_inc_ref(v_toConstantVal_4155_);
v_numParams_4156_ = lean_ctor_get(v_val_4152_, 1);
lean_inc(v_numParams_4156_);
v_all_4157_ = lean_ctor_get(v_val_4152_, 3);
lean_inc(v_all_4157_);
v_numNested_4158_ = lean_ctor_get(v_val_4152_, 5);
lean_inc(v_numNested_4158_);
lean_dec_ref(v_val_4152_);
v_type_4159_ = lean_ctor_get(v_toConstantVal_4155_, 2);
lean_inc_ref(v_type_4159_);
lean_dec_ref(v_toConstantVal_4155_);
v___x_4160_ = l_Lean_Meta_isPropFormerType(v_type_4159_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; uint8_t v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = lean_unbox(v_a_4161_);
lean_dec(v_a_4161_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_inc_n(v_indName_3977_, 2);
v___x_4163_ = l_Lean_mkRecName(v_indName_3977_);
v___x_4164_ = l_Lean_mkBRecOnName(v_indName_3977_);
lean_inc(v_all_4157_);
v___x_4165_ = lean_array_mk(v_all_4157_);
lean_inc(v___x_4164_);
lean_inc_ref(v___x_4165_);
lean_inc(v_numParams_4156_);
lean_inc(v___x_4163_);
v___x_4166_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4163_, v_numParams_4156_, v___x_4165_, v___x_4164_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; uint8_t v___x_4169_; 
lean_dec_ref_known(v___x_4166_, 1);
v___x_4167_ = lean_unsigned_to_nat(0u);
v___x_4168_ = l_List_get_x21Internal___redArg(v___x_3987_, v_all_4157_, v___x_4167_);
lean_dec(v_all_4157_);
v___x_4169_ = lean_name_eq(v___x_4168_, v_indName_3977_);
lean_dec(v_indName_3977_);
lean_dec(v___x_4168_);
if (v___x_4169_ == 0)
{
lean_object* v___x_4170_; 
lean_dec_ref(v___x_4165_);
lean_dec(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v_numNested_4158_);
lean_dec(v_numParams_4156_);
v___x_4170_ = lean_box(0);
v___y_4105_ = v_a_4116_;
v___y_4106_ = v___x_4149_;
v_a_4107_ = v___x_4170_;
goto v___jp_4104_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_box(0);
v___x_4172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4158_, v___x_4163_, v___x_4164_, v_numParams_4156_, v___x_4165_, v___x_4167_, v___x_4171_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_);
lean_dec(v_numNested_4158_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_dec_ref_known(v___x_4172_, 1);
v___y_4105_ = v_a_4116_;
v___y_4106_ = v___x_4149_;
v_a_4107_ = v___x_4171_;
goto v___jp_4104_;
}
else
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v___y_4110_ = v_a_4116_;
v___y_4111_ = v___x_4149_;
v_a_4112_ = v_a_4173_;
goto v___jp_4109_;
}
}
}
else
{
lean_object* v_a_4174_; 
lean_dec_ref(v___x_4165_);
lean_dec(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v_numNested_4158_);
lean_dec(v_all_4157_);
lean_dec(v_numParams_4156_);
lean_dec(v_indName_3977_);
v_a_4174_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4166_, 1);
v___y_4110_ = v_a_4116_;
v___y_4111_ = v___x_4149_;
v_a_4112_ = v_a_4174_;
goto v___jp_4109_;
}
}
else
{
lean_object* v___x_4175_; 
lean_dec(v_numNested_4158_);
lean_dec(v_all_4157_);
lean_dec(v_numParams_4156_);
lean_dec(v_indName_3977_);
v___x_4175_ = lean_box(0);
v___y_4105_ = v_a_4116_;
v___y_4106_ = v___x_4149_;
v_a_4107_ = v___x_4175_;
goto v___jp_4104_;
}
}
else
{
lean_object* v_a_4176_; 
lean_dec(v_numNested_4158_);
lean_dec(v_all_4157_);
lean_dec(v_numParams_4156_);
lean_dec(v_indName_3977_);
v_a_4176_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4160_, 1);
v___y_4110_ = v_a_4116_;
v___y_4111_ = v___x_4149_;
v_a_4112_ = v_a_4176_;
goto v___jp_4109_;
}
}
}
else
{
lean_object* v___x_4177_; 
lean_dec(v_a_4151_);
lean_dec(v_indName_3977_);
v___x_4177_ = lean_box(0);
v___y_4105_ = v_a_4116_;
v___y_4106_ = v___x_4149_;
v_a_4107_ = v___x_4177_;
goto v___jp_4104_;
}
}
else
{
lean_object* v_a_4178_; 
lean_dec(v_indName_3977_);
v_a_4178_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4150_, 1);
v___y_4110_ = v_a_4116_;
v___y_4111_ = v___x_4149_;
v_a_4112_ = v_a_4178_;
goto v___jp_4109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_mkBRecOn(v_indName_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v___x_4265_, lean_object* v___x_4266_, lean_object* v_inst_4267_, lean_object* v_R_4268_, lean_object* v_a_4269_, lean_object* v_b_4270_, lean_object* v_c_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4262_, v___x_4263_, v___x_4264_, v___x_4265_, v___x_4266_, v_a_4269_, v_b_4270_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4278_, lean_object* v___x_4279_, lean_object* v___x_4280_, lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v_inst_4283_, lean_object* v_R_4284_, lean_object* v_a_4285_, lean_object* v_b_4286_, lean_object* v_c_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4278_, v___x_4279_, v___x_4280_, v___x_4281_, v___x_4282_, v_inst_4283_, v_R_4284_, v_a_4285_, v_b_4286_, v_c_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v_upperBound_4278_);
return v_res_4293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = lean_unsigned_to_nat(2304625798u);
v___x_4340_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4341_ = l_Lean_Name_num___override(v___x_4340_, v___x_4339_);
return v___x_4341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4344_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4345_ = l_Lean_Name_str___override(v___x_4344_, v___x_4343_);
return v___x_4345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4348_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4349_ = l_Lean_Name_str___override(v___x_4348_, v___x_4347_);
return v___x_4349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4350_ = lean_unsigned_to_nat(2u);
v___x_4351_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4352_ = l_Lean_Name_num___override(v___x_4351_, v___x_4350_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4354_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4355_ = 0;
v___x_4356_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4357_ = l_Lean_registerTraceClass(v___x_4354_, v___x_4355_, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4359_;
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
