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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26;
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
lean_object* v___f_435_; lean_object* v___x_5213__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_5213__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_5213__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
uint8_t v___x_9579__boxed_554_; lean_object* v_res_555_; 
v___x_9579__boxed_554_ = lean_unbox(v___x_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_545_, v___x_9579__boxed_554_, v_targs_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
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
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
lean_ctor_set(v___x_840_, 2, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_841_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__4);
v___x_842_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
v___x_843_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_844_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
v___x_845_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
lean_ctor_set(v___x_845_, 2, v___x_842_);
lean_ctor_set(v___x_845_, 3, v___x_843_);
lean_ctor_set(v___x_845_, 4, v___x_843_);
lean_ctor_set(v___x_845_, 5, v___x_843_);
lean_ctor_set(v___x_845_, 6, v___x_841_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_846_, uint8_t v_s_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_env_852_; lean_object* v_nextMacroScope_853_; lean_object* v_ngen_854_; lean_object* v_auxDeclNGen_855_; lean_object* v_traceState_856_; lean_object* v_recordedDeps_857_; lean_object* v_messages_858_; lean_object* v_infoState_859_; lean_object* v_snapshotTasks_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_889_; 
v___x_851_ = lean_st_ref_take(v___y_849_);
v_env_852_ = lean_ctor_get(v___x_851_, 0);
v_nextMacroScope_853_ = lean_ctor_get(v___x_851_, 1);
v_ngen_854_ = lean_ctor_get(v___x_851_, 2);
v_auxDeclNGen_855_ = lean_ctor_get(v___x_851_, 3);
v_traceState_856_ = lean_ctor_get(v___x_851_, 4);
v_recordedDeps_857_ = lean_ctor_get(v___x_851_, 6);
v_messages_858_ = lean_ctor_get(v___x_851_, 7);
v_infoState_859_ = lean_ctor_get(v___x_851_, 8);
v_snapshotTasks_860_ = lean_ctor_get(v___x_851_, 9);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_851_, 5);
lean_dec(v_unused_890_);
v___x_862_ = v___x_851_;
v_isShared_863_ = v_isSharedCheck_889_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snapshotTasks_860_);
lean_inc(v_infoState_859_);
lean_inc(v_messages_858_);
lean_inc(v_recordedDeps_857_);
lean_inc(v_traceState_856_);
lean_inc(v_auxDeclNGen_855_);
lean_inc(v_ngen_854_);
lean_inc(v_nextMacroScope_853_);
lean_inc(v_env_852_);
lean_dec(v___x_851_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_889_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_864_ = 0;
v___x_865_ = lean_box(0);
v___x_866_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_852_, v_declName_846_, v_s_847_, v___x_864_, v___x_865_);
v___x_867_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 5, v___x_867_);
lean_ctor_set(v___x_862_, 0, v___x_866_);
v___x_869_ = v___x_862_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_nextMacroScope_853_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_ngen_854_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_auxDeclNGen_855_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_traceState_856_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v___x_867_);
lean_ctor_set(v_reuseFailAlloc_888_, 6, v_recordedDeps_857_);
lean_ctor_set(v_reuseFailAlloc_888_, 7, v_messages_858_);
lean_ctor_set(v_reuseFailAlloc_888_, 8, v_infoState_859_);
lean_ctor_set(v_reuseFailAlloc_888_, 9, v_snapshotTasks_860_);
v___x_869_ = v_reuseFailAlloc_888_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_mctx_872_; lean_object* v_zetaDeltaFVarIds_873_; lean_object* v_postponed_874_; lean_object* v_diag_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
v___x_870_ = lean_st_ref_put(v___y_849_, v___x_869_);
v___x_871_ = lean_st_ref_take(v___y_848_);
v_mctx_872_ = lean_ctor_get(v___x_871_, 0);
v_zetaDeltaFVarIds_873_ = lean_ctor_get(v___x_871_, 2);
v_postponed_874_ = lean_ctor_get(v___x_871_, 3);
v_diag_875_ = lean_ctor_get(v___x_871_, 4);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_871_, 1);
lean_dec(v_unused_887_);
v___x_877_ = v___x_871_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_diag_875_);
lean_inc(v_postponed_874_);
lean_inc(v_zetaDeltaFVarIds_873_);
lean_inc(v_mctx_872_);
lean_dec(v___x_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_mctx_872_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_zetaDeltaFVarIds_873_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_postponed_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_diag_875_);
v___x_882_ = v_reuseFailAlloc_885_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_st_ref_put(v___y_848_, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v___x_879_);
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_891_, lean_object* v_s_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_s_boxed_896_; lean_object* v_res_897_; 
v_s_boxed_896_ = lean_unbox(v_s_892_);
v_res_897_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_891_, v_s_boxed_896_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec(v___y_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_904_; lean_object* v___x_905_; 
v___x_904_ = 0;
v___x_905_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_898_, v___x_904_, v___y_900_, v___y_902_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(lean_object* v_ref_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_toCold_920_; lean_object* v_currRecDepth_921_; lean_object* v_ref_922_; uint16_t v_optionFlags_923_; uint8_t v_suppressElabErrors_924_; uint8_t v_checkDeprecated_925_; uint8_t v_isRecordingDeps_926_; lean_object* v_ref_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_toCold_920_ = lean_ctor_get(v___y_917_, 0);
v_currRecDepth_921_ = lean_ctor_get(v___y_917_, 1);
v_ref_922_ = lean_ctor_get(v___y_917_, 2);
v_optionFlags_923_ = lean_ctor_get_uint16(v___y_917_, sizeof(void*)*3);
v_suppressElabErrors_924_ = lean_ctor_get_uint8(v___y_917_, sizeof(void*)*3 + 2);
v_checkDeprecated_925_ = lean_ctor_get_uint8(v___y_917_, sizeof(void*)*3 + 3);
v_isRecordingDeps_926_ = lean_ctor_get_uint8(v___y_917_, sizeof(void*)*3 + 4);
v_ref_927_ = l_Lean_replaceRef(v_ref_913_, v_ref_922_);
lean_inc(v_currRecDepth_921_);
lean_inc_ref(v_toCold_920_);
v___x_928_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_928_, 0, v_toCold_920_);
lean_ctor_set(v___x_928_, 1, v_currRecDepth_921_);
lean_ctor_set(v___x_928_, 2, v_ref_927_);
lean_ctor_set_uint16(v___x_928_, sizeof(void*)*3, v_optionFlags_923_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3 + 2, v_suppressElabErrors_924_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3 + 3, v_checkDeprecated_925_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3 + 4, v_isRecordingDeps_926_);
v___x_929_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_914_, v___y_915_, v___y_916_, v___x_928_, v___y_918_);
lean_dec_ref_known(v___x_928_, 3);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg___boxed(lean_object* v_ref_930_, lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_930_, v_msg_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v_ref_930_);
return v_res_937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11___redArg___closed__0);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_ctor_set(v___x_942_, 3, v___x_941_);
lean_ctor_set(v___x_942_, 4, v___x_940_);
lean_ctor_set(v___x_942_, 5, v___x_940_);
lean_ctor_set(v___x_942_, 6, v___x_940_);
lean_ctor_set(v___x_942_, 7, v___x_940_);
lean_ctor_set(v___x_942_, 8, v___x_940_);
lean_ctor_set(v___x_942_, 9, v___x_940_);
lean_ctor_set(v___x_942_, 10, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_unsigned_to_nat(32u);
v___x_944_ = lean_mk_empty_array_with_capacity(v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3(void){
_start:
{
size_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_946_ = ((size_t)5ULL);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_unsigned_to_nat(32u);
v___x_949_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_950_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__2);
v___x_951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_947_);
lean_ctor_set(v___x_951_, 3, v___x_947_);
lean_ctor_set_usize(v___x_951_, 4, v___x_946_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_952_ = lean_box(1);
v___x_953_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__3);
v___x_954_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__0);
v___x_955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
lean_ctor_set(v___x_955_, 2, v___x_952_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__5));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__7));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__9));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__11));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__13));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__15));
v___x_973_ = l_Lean_stringToMessageData(v___x_972_);
return v___x_973_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__17));
v___x_976_ = l_Lean_stringToMessageData(v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__19));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__21));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__23));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__25));
v___x_988_ = l_Lean_stringToMessageData(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(lean_object* v_msg_989_, lean_object* v_declHint_990_, lean_object* v___y_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_env_995_; uint8_t v___x_996_; 
v___x_993_ = lean_box(0);
v___x_994_ = lean_st_ref_get(v___y_991_);
v_env_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc_ref(v_env_995_);
lean_dec(v___x_994_);
v___x_996_ = l_Lean_Name_isAnonymous(v_declHint_990_);
if (v___x_996_ == 0)
{
uint8_t v_isExporting_997_; 
v_isExporting_997_ = lean_ctor_get_uint8(v_env_995_, sizeof(void*)*13);
if (v_isExporting_997_ == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v_env_995_);
lean_dec(v_declHint_990_);
v___x_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_998_, 0, v_msg_989_);
return v___x_998_;
}
else
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
lean_inc_ref(v_env_995_);
v___x_999_ = l_Lean_Environment_setExporting(v_env_995_, v___x_996_);
lean_inc(v_declHint_990_);
lean_inc_ref(v___x_999_);
v___x_1000_ = l_Lean_Environment_contains(v___x_999_, v_declHint_990_, v_isExporting_997_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref(v___x_999_);
lean_dec_ref(v_env_995_);
lean_dec(v_declHint_990_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_msg_989_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_c_1007_; lean_object* v___x_1008_; 
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1);
v___x_1003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4);
v___x_1004_ = l_Lean_Options_empty;
lean_inc_ref(v___x_999_);
v___x_1005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1005_, 0, v___x_999_);
lean_ctor_set(v___x_1005_, 1, v___x_1002_);
lean_ctor_set(v___x_1005_, 2, v___x_1003_);
lean_ctor_set(v___x_1005_, 3, v___x_1004_);
lean_inc(v_declHint_990_);
v___x_1006_ = l_Lean_MessageData_ofConstName(v_declHint_990_, v___x_996_);
v_c_1007_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1007_, 0, v___x_1005_);
lean_ctor_set(v_c_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_999_, v_declHint_990_);
lean_dec_ref(v___x_999_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec_ref(v_env_995_);
lean_dec(v_declHint_990_);
v___x_1009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v_c_1007_);
v___x_1011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_MessageData_note(v___x_1012_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_msg_989_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1069_; 
v_val_1016_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1018_ = v___x_1008_;
v_isShared_1019_ = v_isSharedCheck_1069_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_val_1016_);
lean_dec(v___x_1008_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1069_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v_modules_1021_; lean_object* v_moduleNames_1022_; lean_object* v_mod_1023_; uint8_t v___x_1038_; 
v___x_1020_ = l_Lean_Environment_header(v_env_995_);
lean_dec_ref(v_env_995_);
v_modules_1021_ = lean_ctor_get(v___x_1020_, 3);
lean_inc_ref(v_modules_1021_);
v_moduleNames_1022_ = lean_ctor_get(v___x_1020_, 4);
lean_inc_ref(v_moduleNames_1022_);
lean_dec_ref(v___x_1020_);
v_mod_1023_ = lean_array_get(v___x_993_, v_moduleNames_1022_, v_val_1016_);
lean_dec_ref(v_moduleNames_1022_);
v___x_1038_ = l_Lean_isPrivateName(v_declHint_990_);
lean_dec(v_declHint_990_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = lean_array_get_size(v_modules_1021_);
v___x_1040_ = lean_nat_dec_lt(v_val_1016_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec_ref(v_modules_1021_);
lean_dec(v_val_1016_);
goto v___jp_1024_;
}
else
{
lean_object* v___x_1041_; lean_object* v_toImport_1042_; uint8_t v_isExported_1043_; 
v___x_1041_ = lean_array_fget(v_modules_1021_, v_val_1016_);
lean_dec(v_val_1016_);
lean_dec_ref(v_modules_1021_);
v_toImport_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc_ref(v_toImport_1042_);
lean_dec(v___x_1041_);
v_isExported_1043_ = lean_ctor_get_uint8(v_toImport_1042_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1042_);
if (v_isExported_1043_ == 0)
{
goto v___jp_1024_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_del_object(v___x_1018_);
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1007_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofName(v_mod_1023_);
lean_inc_ref(v___x_1048_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__20);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_1048_);
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__22);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_MessageData_note(v___x_1054_);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_msg_989_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref(v_modules_1021_);
lean_del_object(v___x_1018_);
lean_dec(v_val_1016_);
v___x_1058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_c_1007_);
v___x_1060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__24);
v___x_1061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_MessageData_ofName(v_mod_1023_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__26);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = l_Lean_MessageData_note(v___x_1065_);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v_msg_989_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
return v___x_1068_;
}
v___jp_1024_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_c_1007_);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_ofName(v_mod_1023_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_MessageData_note(v___x_1032_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_msg_989_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1034_);
v___x_1036_ = v___x_1018_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1070_; 
lean_dec_ref(v_env_995_);
lean_dec(v_declHint_990_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_msg_989_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_msg_1071_, lean_object* v_declHint_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1071_, v_declHint_1072_, v___y_1073_);
lean_dec(v___y_1073_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(lean_object* v_msg_1076_, lean_object* v_declHint_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1093_; 
v___x_1083_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1076_, v_declHint_1077_, v___y_1081_);
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1086_ = v___x_1083_;
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1083_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1093_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1088_ = l_Lean_unknownIdentifierMessageTag;
v___x_1089_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1084_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1089_);
v___x_1091_ = v___x_1086_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14___boxed(lean_object* v_msg_1094_, lean_object* v_declHint_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1094_, v_declHint_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_ref_1102_, lean_object* v_msg_1103_, lean_object* v_declHint_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_a_1111_; lean_object* v___x_1112_; 
v___x_1110_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1103_, v_declHint_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v___x_1110_);
v___x_1112_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1102_, v_a_1111_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object* v_ref_1113_, lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1113_, v_msg_1114_, v_declHint_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_ref_1113_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1127_ = l_Lean_stringToMessageData(v___x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1128_, lean_object* v_constName_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1135_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1136_ = 0;
lean_inc(v_constName_1129_);
v___x_1137_ = l_Lean_MessageData_ofConstName(v_constName_1129_, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1135_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1138_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1128_, v___x_1140_, v_constName_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1142_, lean_object* v_constName_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1142_, v_constName_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v_ref_1142_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_ref_1156_; lean_object* v___x_1157_; 
v_ref_1156_ = lean_ctor_get(v___y_1153_, 2);
v___x_1157_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1156_, v_constName_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___x_1171_; lean_object* v_env_1172_; uint8_t v___x_1173_; lean_object* v___x_1174_; 
v___x_1171_ = lean_st_ref_get(v___y_1169_);
v_env_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc_ref(v_env_1172_);
lean_dec(v___x_1171_);
v___x_1173_ = 0;
lean_inc(v_constName_1165_);
v___x_1174_ = l_Lean_Environment_find_x3f(v_env_1172_, v_constName_1165_, v___x_1173_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1175_;
}
else
{
lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_constName_1165_);
v_val_1176_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1174_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_dec(v___x_1174_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 0);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_val_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
return v_res_1190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1193_ = l_Lean_stringToMessageData(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1196_ = l_Lean_stringToMessageData(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1199_ = l_Lean_stringToMessageData(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1200_, lean_object* v_nParams_1201_, lean_object* v_belowName_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1200_);
v___x_1209_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1200_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
if (lean_obj_tag(v_a_1210_) == 7)
{
lean_object* v_val_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1328_; 
v_val_1211_ = lean_ctor_get(v_a_1210_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1213_ = v_a_1210_;
v_isShared_1214_ = v_isSharedCheck_1328_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_val_1211_);
lean_dec(v_a_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1328_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_toConstantVal_1215_; lean_object* v_numMotives_1216_; lean_object* v_numMinors_1217_; lean_object* v_levelParams_1218_; lean_object* v_type_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_toConstantVal_1215_ = lean_ctor_get(v_val_1211_, 0);
lean_inc_ref(v_toConstantVal_1215_);
v_numMotives_1216_ = lean_ctor_get(v_val_1211_, 4);
lean_inc(v_numMotives_1216_);
v_numMinors_1217_ = lean_ctor_get(v_val_1211_, 5);
lean_inc(v_numMinors_1217_);
lean_dec_ref(v_val_1211_);
v_levelParams_1218_ = lean_ctor_get(v_toConstantVal_1215_, 1);
lean_inc_n(v_levelParams_1218_, 2);
v_type_1219_ = lean_ctor_get(v_toConstantVal_1215_, 2);
lean_inc_ref(v_type_1219_);
lean_dec_ref(v_toConstantVal_1215_);
v___x_1220_ = lean_box(0);
v___x_1221_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1218_, v___x_1220_);
if (lean_obj_tag(v___x_1221_) == 1)
{
lean_object* v_head_1222_; lean_object* v_tail_1223_; lean_object* v___f_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
v_head_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_head_1222_);
v_tail_1223_ = lean_ctor_get(v___x_1221_, 1);
lean_inc(v_tail_1223_);
lean_dec_ref_known(v___x_1221_, 2);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1224_, 0, v_nParams_1201_);
lean_closure_set(v___f_1224_, 1, v_numMotives_1216_);
lean_closure_set(v___f_1224_, 2, v_numMinors_1217_);
lean_closure_set(v___f_1224_, 3, v___x_1208_);
lean_closure_set(v___f_1224_, 4, v_head_1222_);
lean_closure_set(v___f_1224_, 5, v_tail_1223_);
lean_closure_set(v___f_1224_, 6, v_recName_1200_);
lean_closure_set(v___f_1224_, 7, v_belowName_1202_);
lean_closure_set(v___f_1224_, 8, v_levelParams_1218_);
v___x_1225_ = 0;
v___x_1226_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1219_, v___f_1224_, v___x_1225_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_n(v_a_1227_, 2);
lean_dec_ref_known(v___x_1226_, 1);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
lean_ctor_set(v___x_1213_, 0, v_a_1227_);
v___x_1229_ = v___x_1213_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1227_);
v___x_1229_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Lean_addDecl(v___x_1229_, v___x_1225_, v_a_1205_, v_a_1206_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_toConstantVal_1231_; lean_object* v_name_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref_known(v___x_1230_, 1);
v_toConstantVal_1231_ = lean_ctor_get(v_a_1227_, 0);
lean_inc_ref(v_toConstantVal_1231_);
lean_dec(v_a_1227_);
v_name_1232_ = lean_ctor_get(v_toConstantVal_1231_, 0);
lean_inc_n(v_name_1232_, 2);
lean_dec_ref(v_toConstantVal_1231_);
v___x_1233_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1232_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v___x_1233_, 0);
lean_dec(v_unused_1312_);
v___x_1235_ = v___x_1233_;
v_isShared_1236_ = v_isSharedCheck_1311_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v___x_1233_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1311_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v_env_1238_; lean_object* v_nextMacroScope_1239_; lean_object* v_ngen_1240_; lean_object* v_auxDeclNGen_1241_; lean_object* v_traceState_1242_; lean_object* v_recordedDeps_1243_; lean_object* v_messages_1244_; lean_object* v_infoState_1245_; lean_object* v_snapshotTasks_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1309_; 
v___x_1237_ = lean_st_ref_take(v_a_1206_);
v_env_1238_ = lean_ctor_get(v___x_1237_, 0);
v_nextMacroScope_1239_ = lean_ctor_get(v___x_1237_, 1);
v_ngen_1240_ = lean_ctor_get(v___x_1237_, 2);
v_auxDeclNGen_1241_ = lean_ctor_get(v___x_1237_, 3);
v_traceState_1242_ = lean_ctor_get(v___x_1237_, 4);
v_recordedDeps_1243_ = lean_ctor_get(v___x_1237_, 6);
v_messages_1244_ = lean_ctor_get(v___x_1237_, 7);
v_infoState_1245_ = lean_ctor_get(v___x_1237_, 8);
v_snapshotTasks_1246_ = lean_ctor_get(v___x_1237_, 9);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v___x_1237_, 5);
lean_dec(v_unused_1310_);
v___x_1248_ = v___x_1237_;
v_isShared_1249_ = v_isSharedCheck_1309_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_snapshotTasks_1246_);
lean_inc(v_infoState_1245_);
lean_inc(v_messages_1244_);
lean_inc(v_recordedDeps_1243_);
lean_inc(v_traceState_1242_);
lean_inc(v_auxDeclNGen_1241_);
lean_inc(v_ngen_1240_);
lean_inc(v_nextMacroScope_1239_);
lean_inc(v_env_1238_);
lean_dec(v___x_1237_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1309_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_inc(v_name_1232_);
v___x_1250_ = l_Lean_markAuxRecursor(v_env_1238_, v_name_1232_);
v___x_1251_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 5, v___x_1251_);
lean_ctor_set(v___x_1248_, 0, v___x_1250_);
v___x_1253_ = v___x_1248_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_nextMacroScope_1239_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_ngen_1240_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_auxDeclNGen_1241_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v_traceState_1242_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1308_, 6, v_recordedDeps_1243_);
lean_ctor_set(v_reuseFailAlloc_1308_, 7, v_messages_1244_);
lean_ctor_set(v_reuseFailAlloc_1308_, 8, v_infoState_1245_);
lean_ctor_set(v_reuseFailAlloc_1308_, 9, v_snapshotTasks_1246_);
v___x_1253_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v_mctx_1256_; lean_object* v_zetaDeltaFVarIds_1257_; lean_object* v_postponed_1258_; lean_object* v_diag_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1306_; 
v___x_1254_ = lean_st_ref_put(v_a_1206_, v___x_1253_);
v___x_1255_ = lean_st_ref_take(v_a_1204_);
v_mctx_1256_ = lean_ctor_get(v___x_1255_, 0);
v_zetaDeltaFVarIds_1257_ = lean_ctor_get(v___x_1255_, 2);
v_postponed_1258_ = lean_ctor_get(v___x_1255_, 3);
v_diag_1259_ = lean_ctor_get(v___x_1255_, 4);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v___x_1255_, 1);
lean_dec(v_unused_1307_);
v___x_1261_ = v___x_1255_;
v_isShared_1262_ = v_isSharedCheck_1306_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_diag_1259_);
lean_inc(v_postponed_1258_);
lean_inc(v_zetaDeltaFVarIds_1257_);
lean_inc(v_mctx_1256_);
lean_dec(v___x_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1306_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1263_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_mctx_1256_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_zetaDeltaFVarIds_1257_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_postponed_1258_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v_diag_1259_);
v___x_1265_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_env_1268_; lean_object* v_nextMacroScope_1269_; lean_object* v_ngen_1270_; lean_object* v_auxDeclNGen_1271_; lean_object* v_traceState_1272_; lean_object* v_recordedDeps_1273_; lean_object* v_messages_1274_; lean_object* v_infoState_1275_; lean_object* v_snapshotTasks_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1303_; 
v___x_1266_ = lean_st_ref_put(v_a_1204_, v___x_1265_);
v___x_1267_ = lean_st_ref_take(v_a_1206_);
v_env_1268_ = lean_ctor_get(v___x_1267_, 0);
v_nextMacroScope_1269_ = lean_ctor_get(v___x_1267_, 1);
v_ngen_1270_ = lean_ctor_get(v___x_1267_, 2);
v_auxDeclNGen_1271_ = lean_ctor_get(v___x_1267_, 3);
v_traceState_1272_ = lean_ctor_get(v___x_1267_, 4);
v_recordedDeps_1273_ = lean_ctor_get(v___x_1267_, 6);
v_messages_1274_ = lean_ctor_get(v___x_1267_, 7);
v_infoState_1275_ = lean_ctor_get(v___x_1267_, 8);
v_snapshotTasks_1276_ = lean_ctor_get(v___x_1267_, 9);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; 
v_unused_1304_ = lean_ctor_get(v___x_1267_, 5);
lean_dec(v_unused_1304_);
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1303_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snapshotTasks_1276_);
lean_inc(v_infoState_1275_);
lean_inc(v_messages_1274_);
lean_inc(v_recordedDeps_1273_);
lean_inc(v_traceState_1272_);
lean_inc(v_auxDeclNGen_1271_);
lean_inc(v_ngen_1270_);
lean_inc(v_nextMacroScope_1269_);
lean_inc(v_env_1268_);
lean_dec(v___x_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1303_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = l_Lean_addProtected(v_env_1268_, v_name_1232_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 5, v___x_1251_);
lean_ctor_set(v___x_1278_, 0, v___x_1280_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_nextMacroScope_1269_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_ngen_1270_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_auxDeclNGen_1271_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_traceState_1272_);
lean_ctor_set(v_reuseFailAlloc_1302_, 5, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1302_, 6, v_recordedDeps_1273_);
lean_ctor_set(v_reuseFailAlloc_1302_, 7, v_messages_1274_);
lean_ctor_set(v_reuseFailAlloc_1302_, 8, v_infoState_1275_);
lean_ctor_set(v_reuseFailAlloc_1302_, 9, v_snapshotTasks_1276_);
v___x_1282_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v_mctx_1285_; lean_object* v_zetaDeltaFVarIds_1286_; lean_object* v_postponed_1287_; lean_object* v_diag_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1300_; 
v___x_1283_ = lean_st_ref_put(v_a_1206_, v___x_1282_);
v___x_1284_ = lean_st_ref_take(v_a_1204_);
v_mctx_1285_ = lean_ctor_get(v___x_1284_, 0);
v_zetaDeltaFVarIds_1286_ = lean_ctor_get(v___x_1284_, 2);
v_postponed_1287_ = lean_ctor_get(v___x_1284_, 3);
v_diag_1288_ = lean_ctor_get(v___x_1284_, 4);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1284_, 1);
lean_dec(v_unused_1301_);
v___x_1290_ = v___x_1284_;
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_diag_1288_);
lean_inc(v_postponed_1287_);
lean_inc(v_zetaDeltaFVarIds_1286_);
lean_inc(v_mctx_1285_);
lean_dec(v___x_1284_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_box(0);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 1, v___x_1263_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_mctx_1285_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_zetaDeltaFVarIds_1286_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_postponed_1287_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_diag_1288_);
v___x_1294_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
v___x_1295_ = lean_st_ref_put(v_a_1204_, v___x_1294_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1292_);
v___x_1297_ = v___x_1235_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
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
lean_dec(v_a_1227_);
return v___x_1230_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_del_object(v___x_1213_);
v_a_1314_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1226_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1226_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v___x_1221_);
lean_dec_ref(v_type_1219_);
lean_dec(v_levelParams_1218_);
lean_dec(v_numMinors_1217_);
lean_dec(v_numMotives_1216_);
lean_del_object(v___x_1213_);
lean_dec(v_belowName_1202_);
lean_dec(v_nParams_1201_);
v___x_1322_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1323_ = l_Lean_MessageData_ofName(v_recName_1200_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1326_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1327_;
}
}
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec(v_a_1210_);
lean_dec(v_belowName_1202_);
lean_dec(v_nParams_1201_);
v___x_1329_ = l_Lean_MessageData_ofName(v_recName_1200_);
v___x_1330_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1329_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1331_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
return v___x_1332_;
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_belowName_1202_);
lean_dec(v_nParams_1201_);
lean_dec(v_recName_1200_);
v_a_1333_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1209_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1209_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1341_, lean_object* v_nParams_1342_, lean_object* v_belowName_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1341_, v_nParams_1342_, v_belowName_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1358_, lean_object* v_msg_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1358_, v_msg_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11(lean_object* v_00_u03b2_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg(){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg___boxed(lean_object* v___dummy_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg();
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8(lean_object* v_00_u03b2_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1374_, lean_object* v_constName_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1382_, v_constName_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1390_, uint8_t v_s_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1390_, v_s_1391_, v___y_1393_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1398_, lean_object* v_s_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v_s_boxed_1405_; lean_object* v_res_1406_; 
v_s_boxed_1405_ = lean_unbox(v_s_1399_);
v_res_1406_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1398_, v_s_boxed_1405_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1407_, lean_object* v_ref_1408_, lean_object* v_constName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1408_, v_constName_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_ref_1417_, lean_object* v_constName_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1416_, v_ref_1417_, v_constName_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v_ref_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b1_1425_, lean_object* v_ref_1426_, lean_object* v_msg_1427_, lean_object* v_declHint_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1426_, v_msg_1427_, v_declHint_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_ref_1436_, lean_object* v_msg_1437_, lean_object* v_declHint_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(v_00_u03b1_1435_, v_ref_1436_, v_msg_1437_, v_declHint_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v_ref_1436_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(lean_object* v_msg_1445_, lean_object* v_declHint_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1445_, v_declHint_1446_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_1453_, lean_object* v_declHint_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(v_msg_1453_, v_declHint_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(lean_object* v_00_u03b1_1461_, lean_object* v_ref_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1462_, v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(v_00_u03b1_1470_, v_ref_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v_ref_1471_);
return v_res_1478_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_unsigned_to_nat(32u);
v___x_1480_ = lean_mk_empty_array_with_capacity(v___x_1479_);
v___x_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
return v___x_1481_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1482_ = ((size_t)5ULL);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = lean_unsigned_to_nat(32u);
v___x_1485_ = lean_mk_empty_array_with_capacity(v___x_1484_);
v___x_1486_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1487_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v___x_1485_);
lean_ctor_set(v___x_1487_, 2, v___x_1483_);
lean_ctor_set(v___x_1487_, 3, v___x_1483_);
lean_ctor_set_usize(v___x_1487_, 4, v___x_1482_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v_traceState_1491_; lean_object* v_traces_1492_; lean_object* v___x_1493_; lean_object* v_traceState_1494_; lean_object* v_env_1495_; lean_object* v_nextMacroScope_1496_; lean_object* v_ngen_1497_; lean_object* v_auxDeclNGen_1498_; lean_object* v_cache_1499_; lean_object* v_recordedDeps_1500_; lean_object* v_messages_1501_; lean_object* v_infoState_1502_; lean_object* v_snapshotTasks_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1522_; 
v___x_1490_ = lean_st_ref_get(v___y_1488_);
v_traceState_1491_ = lean_ctor_get(v___x_1490_, 4);
lean_inc_ref(v_traceState_1491_);
lean_dec(v___x_1490_);
v_traces_1492_ = lean_ctor_get(v_traceState_1491_, 0);
lean_inc_ref(v_traces_1492_);
lean_dec_ref(v_traceState_1491_);
v___x_1493_ = lean_st_ref_take(v___y_1488_);
v_traceState_1494_ = lean_ctor_get(v___x_1493_, 4);
v_env_1495_ = lean_ctor_get(v___x_1493_, 0);
v_nextMacroScope_1496_ = lean_ctor_get(v___x_1493_, 1);
v_ngen_1497_ = lean_ctor_get(v___x_1493_, 2);
v_auxDeclNGen_1498_ = lean_ctor_get(v___x_1493_, 3);
v_cache_1499_ = lean_ctor_get(v___x_1493_, 5);
v_recordedDeps_1500_ = lean_ctor_get(v___x_1493_, 6);
v_messages_1501_ = lean_ctor_get(v___x_1493_, 7);
v_infoState_1502_ = lean_ctor_get(v___x_1493_, 8);
v_snapshotTasks_1503_ = lean_ctor_get(v___x_1493_, 9);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1505_ = v___x_1493_;
v_isShared_1506_ = v_isSharedCheck_1522_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_snapshotTasks_1503_);
lean_inc(v_infoState_1502_);
lean_inc(v_messages_1501_);
lean_inc(v_recordedDeps_1500_);
lean_inc(v_cache_1499_);
lean_inc(v_traceState_1494_);
lean_inc(v_auxDeclNGen_1498_);
lean_inc(v_ngen_1497_);
lean_inc(v_nextMacroScope_1496_);
lean_inc(v_env_1495_);
lean_dec(v___x_1493_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1522_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint64_t v_tid_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1520_; 
v_tid_1507_ = lean_ctor_get_uint64(v_traceState_1494_, sizeof(void*)*1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_traceState_1494_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_traceState_1494_, 0);
lean_dec(v_unused_1521_);
v___x_1509_ = v_traceState_1494_;
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_traceState_1494_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1520_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1513_ = v___x_1509_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1511_);
lean_ctor_set_uint64(v_reuseFailAlloc_1519_, sizeof(void*)*1, v_tid_1507_);
v___x_1513_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v___x_1513_);
v___x_1515_ = v___x_1505_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_env_1495_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_nextMacroScope_1496_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_ngen_1497_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_auxDeclNGen_1498_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1518_, 5, v_cache_1499_);
lean_ctor_set(v_reuseFailAlloc_1518_, 6, v_recordedDeps_1500_);
lean_ctor_set(v_reuseFailAlloc_1518_, 7, v_messages_1501_);
lean_ctor_set(v_reuseFailAlloc_1518_, 8, v_infoState_1502_);
lean_ctor_set(v_reuseFailAlloc_1518_, 9, v_snapshotTasks_1503_);
v___x_1515_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_st_ref_put(v___y_1488_, v___x_1515_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_traces_1492_);
return v___x_1517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1523_);
lean_dec(v___y_1523_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1538_, lean_object* v_opt_1539_){
_start:
{
lean_object* v_name_1540_; lean_object* v_defValue_1541_; lean_object* v_map_1542_; lean_object* v___x_1543_; 
v_name_1540_ = lean_ctor_get(v_opt_1539_, 0);
v_defValue_1541_ = lean_ctor_get(v_opt_1539_, 1);
v_map_1542_ = lean_ctor_get(v_opts_1538_, 0);
v___x_1543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1542_, v_name_1540_);
if (lean_obj_tag(v___x_1543_) == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_defValue_1541_);
return v___x_1544_;
}
else
{
lean_object* v_val_1545_; 
v_val_1545_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1543_, 1);
if (lean_obj_tag(v_val_1545_) == 1)
{
uint8_t v_v_1546_; 
v_v_1546_ = lean_ctor_get_uint8(v_val_1545_, 0);
lean_dec_ref_known(v_val_1545_, 0);
return v_v_1546_;
}
else
{
uint8_t v___x_1547_; 
lean_dec(v_val_1545_);
v___x_1547_ = lean_unbox(v_defValue_1541_);
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1548_, lean_object* v_opt_1549_){
_start:
{
uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1548_, v_opt_1549_);
lean_dec_ref(v_opt_1549_);
lean_dec_ref(v_opts_1548_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1552_, lean_object* v_x_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_MessageData_ofName(v_indName_1552_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_mkBelow___lam__0(v_indName_1561_, v_x_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_x_1562_);
return v_res_1568_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1569_){
_start:
{
if (lean_obj_tag(v_e_1569_) == 0)
{
uint8_t v___x_1570_; 
v___x_1570_ = 2;
return v___x_1570_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = 0;
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1572_);
lean_dec_ref(v_e_1572_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1575_){
_start:
{
if (lean_obj_tag(v_x_1575_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
v_a_1577_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v_x_1575_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v_x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v_x_1575_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1575_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v_x_1575_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v_x_1575_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 0);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1596_, lean_object* v_opt_1597_){
_start:
{
lean_object* v_name_1598_; lean_object* v_defValue_1599_; lean_object* v_map_1600_; lean_object* v___x_1601_; 
v_name_1598_ = lean_ctor_get(v_opt_1597_, 0);
v_defValue_1599_ = lean_ctor_get(v_opt_1597_, 1);
v_map_1600_ = lean_ctor_get(v_opts_1596_, 0);
v___x_1601_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1600_, v_name_1598_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_inc(v_defValue_1599_);
return v_defValue_1599_;
}
else
{
lean_object* v_val_1602_; 
v_val_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v___x_1601_, 1);
if (lean_obj_tag(v_val_1602_) == 3)
{
lean_object* v_v_1603_; 
v_v_1603_ = lean_ctor_get(v_val_1602_, 0);
lean_inc(v_v_1603_);
lean_dec_ref_known(v_val_1602_, 1);
return v_v_1603_;
}
else
{
lean_dec(v_val_1602_);
lean_inc(v_defValue_1599_);
return v_defValue_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1604_, lean_object* v_opt_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1604_, v_opt_1605_);
lean_dec_ref(v_opt_1605_);
lean_dec_ref(v_opts_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1607_, size_t v_i_1608_, lean_object* v_bs_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1608_, v_sz_1607_);
if (v___x_1610_ == 0)
{
return v_bs_1609_;
}
else
{
lean_object* v_v_1611_; lean_object* v_msg_1612_; lean_object* v___x_1613_; lean_object* v_bs_x27_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v_v_1611_ = lean_array_uget_borrowed(v_bs_1609_, v_i_1608_);
v_msg_1612_ = lean_ctor_get(v_v_1611_, 1);
lean_inc_ref(v_msg_1612_);
v___x_1613_ = lean_unsigned_to_nat(0u);
v_bs_x27_1614_ = lean_array_uset(v_bs_1609_, v_i_1608_, v___x_1613_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1608_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1614_, v_i_1608_, v_msg_1612_);
v_i_1608_ = v___x_1616_;
v_bs_1609_ = v___x_1617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_bs_1621_){
_start:
{
size_t v_sz_boxed_1622_; size_t v_i_boxed_1623_; lean_object* v_res_1624_; 
v_sz_boxed_1622_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1623_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1622_, v_i_boxed_1623_, v_bs_1621_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1625_, lean_object* v_data_1626_, lean_object* v_ref_1627_, lean_object* v_msg_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_toCold_1634_; lean_object* v_currRecDepth_1635_; lean_object* v_ref_1636_; uint16_t v_optionFlags_1637_; uint8_t v_suppressElabErrors_1638_; uint8_t v_checkDeprecated_1639_; uint8_t v_isRecordingDeps_1640_; lean_object* v_ref_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_traceState_1644_; lean_object* v_traces_1645_; lean_object* v___x_1646_; size_t v_sz_1647_; size_t v___x_1648_; lean_object* v___x_1649_; lean_object* v_msg_1650_; lean_object* v___x_1651_; lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1690_; 
v_toCold_1634_ = lean_ctor_get(v___y_1631_, 0);
v_currRecDepth_1635_ = lean_ctor_get(v___y_1631_, 1);
v_ref_1636_ = lean_ctor_get(v___y_1631_, 2);
v_optionFlags_1637_ = lean_ctor_get_uint16(v___y_1631_, sizeof(void*)*3);
v_suppressElabErrors_1638_ = lean_ctor_get_uint8(v___y_1631_, sizeof(void*)*3 + 2);
v_checkDeprecated_1639_ = lean_ctor_get_uint8(v___y_1631_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1640_ = lean_ctor_get_uint8(v___y_1631_, sizeof(void*)*3 + 4);
v_ref_1641_ = l_Lean_replaceRef(v_ref_1627_, v_ref_1636_);
lean_inc(v_currRecDepth_1635_);
lean_inc_ref(v_toCold_1634_);
v___x_1642_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1642_, 0, v_toCold_1634_);
lean_ctor_set(v___x_1642_, 1, v_currRecDepth_1635_);
lean_ctor_set(v___x_1642_, 2, v_ref_1641_);
lean_ctor_set_uint16(v___x_1642_, sizeof(void*)*3, v_optionFlags_1637_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*3 + 2, v_suppressElabErrors_1638_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*3 + 3, v_checkDeprecated_1639_);
lean_ctor_set_uint8(v___x_1642_, sizeof(void*)*3 + 4, v_isRecordingDeps_1640_);
v___x_1643_ = lean_st_ref_get(v___y_1632_);
v_traceState_1644_ = lean_ctor_get(v___x_1643_, 4);
lean_inc_ref(v_traceState_1644_);
lean_dec(v___x_1643_);
v_traces_1645_ = lean_ctor_get(v_traceState_1644_, 0);
lean_inc_ref(v_traces_1645_);
lean_dec_ref(v_traceState_1644_);
v___x_1646_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1645_);
lean_dec_ref(v_traces_1645_);
v_sz_1647_ = lean_array_size(v___x_1646_);
v___x_1648_ = ((size_t)0ULL);
v___x_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1647_, v___x_1648_, v___x_1646_);
v_msg_1650_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1650_, 0, v_data_1626_);
lean_ctor_set(v_msg_1650_, 1, v_msg_1628_);
lean_ctor_set(v_msg_1650_, 2, v___x_1649_);
v___x_1651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1650_, v___y_1629_, v___y_1630_, v___x_1642_, v___y_1632_);
lean_dec_ref_known(v___x_1642_, 3);
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1690_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1690_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1656_; lean_object* v_traceState_1657_; lean_object* v_env_1658_; lean_object* v_nextMacroScope_1659_; lean_object* v_ngen_1660_; lean_object* v_auxDeclNGen_1661_; lean_object* v_cache_1662_; lean_object* v_recordedDeps_1663_; lean_object* v_messages_1664_; lean_object* v_infoState_1665_; lean_object* v_snapshotTasks_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1689_; 
v___x_1656_ = lean_st_ref_take(v___y_1632_);
v_traceState_1657_ = lean_ctor_get(v___x_1656_, 4);
v_env_1658_ = lean_ctor_get(v___x_1656_, 0);
v_nextMacroScope_1659_ = lean_ctor_get(v___x_1656_, 1);
v_ngen_1660_ = lean_ctor_get(v___x_1656_, 2);
v_auxDeclNGen_1661_ = lean_ctor_get(v___x_1656_, 3);
v_cache_1662_ = lean_ctor_get(v___x_1656_, 5);
v_recordedDeps_1663_ = lean_ctor_get(v___x_1656_, 6);
v_messages_1664_ = lean_ctor_get(v___x_1656_, 7);
v_infoState_1665_ = lean_ctor_get(v___x_1656_, 8);
v_snapshotTasks_1666_ = lean_ctor_get(v___x_1656_, 9);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1668_ = v___x_1656_;
v_isShared_1669_ = v_isSharedCheck_1689_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_snapshotTasks_1666_);
lean_inc(v_infoState_1665_);
lean_inc(v_messages_1664_);
lean_inc(v_recordedDeps_1663_);
lean_inc(v_cache_1662_);
lean_inc(v_traceState_1657_);
lean_inc(v_auxDeclNGen_1661_);
lean_inc(v_ngen_1660_);
lean_inc(v_nextMacroScope_1659_);
lean_inc(v_env_1658_);
lean_dec(v___x_1656_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1689_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint64_t v_tid_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1687_; 
v_tid_1670_ = lean_ctor_get_uint64(v_traceState_1657_, sizeof(void*)*1);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_traceState_1657_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_traceState_1657_, 0);
lean_dec(v_unused_1688_);
v___x_1672_ = v_traceState_1657_;
v_isShared_1673_ = v_isSharedCheck_1687_;
goto v_resetjp_1671_;
}
else
{
lean_dec(v_traceState_1657_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1687_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1674_ = lean_box(0);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_ref_1627_);
lean_ctor_set(v___x_1675_, 1, v_a_1652_);
v___x_1676_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1625_, v___x_1675_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1676_);
v___x_1678_ = v___x_1672_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1676_);
lean_ctor_set_uint64(v_reuseFailAlloc_1686_, sizeof(void*)*1, v_tid_1670_);
v___x_1678_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 4, v___x_1678_);
v___x_1680_ = v___x_1668_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_env_1658_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_nextMacroScope_1659_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_ngen_1660_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_auxDeclNGen_1661_);
lean_ctor_set(v_reuseFailAlloc_1685_, 4, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1685_, 5, v_cache_1662_);
lean_ctor_set(v_reuseFailAlloc_1685_, 6, v_recordedDeps_1663_);
lean_ctor_set(v_reuseFailAlloc_1685_, 7, v_messages_1664_);
lean_ctor_set(v_reuseFailAlloc_1685_, 8, v_infoState_1665_);
lean_ctor_set(v_reuseFailAlloc_1685_, 9, v_snapshotTasks_1666_);
v___x_1680_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_st_ref_put(v___y_1632_, v___x_1680_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1674_);
v___x_1683_ = v___x_1654_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1674_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1691_, lean_object* v_data_1692_, lean_object* v_ref_1693_, lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1691_, v_data_1692_, v_ref_1693_, v_msg_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
return v_res_1700_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1701_; double v___x_1702_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_float_of_nat(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1706_; double v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(1000u);
v___x_1707_ = lean_float_of_nat(v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1708_, uint8_t v_collapsed_1709_, lean_object* v_tag_1710_, lean_object* v_opts_1711_, uint8_t v_clsEnabled_1712_, lean_object* v_oldTraces_1713_, lean_object* v_msg_1714_, lean_object* v_resStartStop_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_fst_1721_; lean_object* v_snd_1722_; lean_object* v___y_1724_; lean_object* v___y_1725_; lean_object* v_data_1726_; lean_object* v_fst_1729_; lean_object* v_snd_1730_; lean_object* v___x_1731_; uint8_t v___x_1732_; lean_object* v___y_1734_; lean_object* v_a_1735_; uint8_t v___y_1750_; double v___y_1782_; 
v_fst_1721_ = lean_ctor_get(v_resStartStop_1715_, 0);
lean_inc(v_fst_1721_);
v_snd_1722_ = lean_ctor_get(v_resStartStop_1715_, 1);
lean_inc(v_snd_1722_);
lean_dec_ref(v_resStartStop_1715_);
v_fst_1729_ = lean_ctor_get(v_snd_1722_, 0);
lean_inc(v_fst_1729_);
v_snd_1730_ = lean_ctor_get(v_snd_1722_, 1);
lean_inc(v_snd_1730_);
lean_dec(v_snd_1722_);
v___x_1731_ = l_Lean_trace_profiler;
v___x_1732_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1711_, v___x_1731_);
if (v___x_1732_ == 0)
{
v___y_1750_ = v___x_1732_;
goto v___jp_1749_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1788_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1711_, v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; double v___x_1791_; double v___x_1792_; double v___x_1793_; 
v___x_1789_ = l_Lean_trace_profiler_threshold;
v___x_1790_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1711_, v___x_1789_);
v___x_1791_ = lean_float_of_nat(v___x_1790_);
v___x_1792_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1793_ = lean_float_div(v___x_1791_, v___x_1792_);
v___y_1782_ = v___x_1793_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; double v___x_1796_; 
v___x_1794_ = l_Lean_trace_profiler_threshold;
v___x_1795_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1711_, v___x_1794_);
v___x_1796_ = lean_float_of_nat(v___x_1795_);
v___y_1782_ = v___x_1796_;
goto v___jp_1781_;
}
}
v___jp_1723_:
{
lean_object* v___x_1727_; 
lean_inc(v___y_1725_);
v___x_1727_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1713_, v_data_1726_, v___y_1725_, v___y_1724_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1728_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1721_);
return v___x_1728_;
}
else
{
lean_dec(v_fst_1721_);
return v___x_1727_;
}
}
v___jp_1733_:
{
uint8_t v_result_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; double v___x_1739_; lean_object* v_data_1740_; 
v_result_1736_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1721_);
v___x_1737_ = lean_box(v_result_1736_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1710_);
lean_inc_ref(v___x_1738_);
lean_inc(v_cls_1708_);
v_data_1740_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1740_, 0, v_cls_1708_);
lean_ctor_set(v_data_1740_, 1, v___x_1738_);
lean_ctor_set(v_data_1740_, 2, v_tag_1710_);
lean_ctor_set_float(v_data_1740_, sizeof(void*)*3, v___x_1739_);
lean_ctor_set_float(v_data_1740_, sizeof(void*)*3 + 8, v___x_1739_);
lean_ctor_set_uint8(v_data_1740_, sizeof(void*)*3 + 16, v_collapsed_1709_);
if (v___x_1732_ == 0)
{
lean_dec_ref_known(v___x_1738_, 1);
lean_dec(v_snd_1730_);
lean_dec(v_fst_1729_);
lean_dec_ref(v_tag_1710_);
lean_dec(v_cls_1708_);
v___y_1724_ = v_a_1735_;
v___y_1725_ = v___y_1734_;
v_data_1726_ = v_data_1740_;
goto v___jp_1723_;
}
else
{
lean_object* v_data_1741_; double v___x_1742_; double v___x_1743_; 
lean_dec_ref_known(v_data_1740_, 3);
v_data_1741_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1741_, 0, v_cls_1708_);
lean_ctor_set(v_data_1741_, 1, v___x_1738_);
lean_ctor_set(v_data_1741_, 2, v_tag_1710_);
v___x_1742_ = lean_unbox_float(v_fst_1729_);
lean_dec(v_fst_1729_);
lean_ctor_set_float(v_data_1741_, sizeof(void*)*3, v___x_1742_);
v___x_1743_ = lean_unbox_float(v_snd_1730_);
lean_dec(v_snd_1730_);
lean_ctor_set_float(v_data_1741_, sizeof(void*)*3 + 8, v___x_1743_);
lean_ctor_set_uint8(v_data_1741_, sizeof(void*)*3 + 16, v_collapsed_1709_);
v___y_1724_ = v_a_1735_;
v___y_1725_ = v___y_1734_;
v_data_1726_ = v_data_1741_;
goto v___jp_1723_;
}
}
v___jp_1744_:
{
lean_object* v_ref_1745_; lean_object* v___x_1746_; 
v_ref_1745_ = lean_ctor_get(v___y_1718_, 2);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1717_);
lean_inc_ref(v___y_1716_);
lean_inc(v_fst_1721_);
v___x_1746_ = lean_apply_6(v_msg_1714_, v_fst_1721_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, lean_box(0));
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___y_1734_ = v_ref_1745_;
v_a_1735_ = v_a_1747_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1748_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1734_ = v_ref_1745_;
v_a_1735_ = v___x_1748_;
goto v___jp_1733_;
}
}
v___jp_1749_:
{
if (v_clsEnabled_1712_ == 0)
{
if (v___y_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v_traceState_1752_; lean_object* v_env_1753_; lean_object* v_nextMacroScope_1754_; lean_object* v_ngen_1755_; lean_object* v_auxDeclNGen_1756_; lean_object* v_cache_1757_; lean_object* v_recordedDeps_1758_; lean_object* v_messages_1759_; lean_object* v_infoState_1760_; lean_object* v_snapshotTasks_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_snd_1730_);
lean_dec(v_fst_1729_);
lean_dec_ref(v_msg_1714_);
lean_dec_ref(v_tag_1710_);
lean_dec(v_cls_1708_);
v___x_1751_ = lean_st_ref_take(v___y_1719_);
v_traceState_1752_ = lean_ctor_get(v___x_1751_, 4);
v_env_1753_ = lean_ctor_get(v___x_1751_, 0);
v_nextMacroScope_1754_ = lean_ctor_get(v___x_1751_, 1);
v_ngen_1755_ = lean_ctor_get(v___x_1751_, 2);
v_auxDeclNGen_1756_ = lean_ctor_get(v___x_1751_, 3);
v_cache_1757_ = lean_ctor_get(v___x_1751_, 5);
v_recordedDeps_1758_ = lean_ctor_get(v___x_1751_, 6);
v_messages_1759_ = lean_ctor_get(v___x_1751_, 7);
v_infoState_1760_ = lean_ctor_get(v___x_1751_, 8);
v_snapshotTasks_1761_ = lean_ctor_get(v___x_1751_, 9);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1763_ = v___x_1751_;
v_isShared_1764_ = v_isSharedCheck_1780_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snapshotTasks_1761_);
lean_inc(v_infoState_1760_);
lean_inc(v_messages_1759_);
lean_inc(v_recordedDeps_1758_);
lean_inc(v_cache_1757_);
lean_inc(v_traceState_1752_);
lean_inc(v_auxDeclNGen_1756_);
lean_inc(v_ngen_1755_);
lean_inc(v_nextMacroScope_1754_);
lean_inc(v_env_1753_);
lean_dec(v___x_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1780_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
uint64_t v_tid_1765_; lean_object* v_traces_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1779_; 
v_tid_1765_ = lean_ctor_get_uint64(v_traceState_1752_, sizeof(void*)*1);
v_traces_1766_ = lean_ctor_get(v_traceState_1752_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_traceState_1752_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1768_ = v_traceState_1752_;
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_traces_1766_);
lean_dec(v_traceState_1752_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1779_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
v___x_1770_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1713_, v_traces_1766_);
lean_dec_ref(v_traces_1766_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1770_);
v___x_1772_ = v___x_1768_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1770_);
lean_ctor_set_uint64(v_reuseFailAlloc_1778_, sizeof(void*)*1, v_tid_1765_);
v___x_1772_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 4, v___x_1772_);
v___x_1774_ = v___x_1763_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_env_1753_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_nextMacroScope_1754_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_ngen_1755_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_auxDeclNGen_1756_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1777_, 5, v_cache_1757_);
lean_ctor_set(v_reuseFailAlloc_1777_, 6, v_recordedDeps_1758_);
lean_ctor_set(v_reuseFailAlloc_1777_, 7, v_messages_1759_);
lean_ctor_set(v_reuseFailAlloc_1777_, 8, v_infoState_1760_);
lean_ctor_set(v_reuseFailAlloc_1777_, 9, v_snapshotTasks_1761_);
v___x_1774_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_st_ref_put(v___y_1719_, v___x_1774_);
v___x_1776_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1721_);
return v___x_1776_;
}
}
}
}
}
else
{
goto v___jp_1744_;
}
}
else
{
goto v___jp_1744_;
}
}
v___jp_1781_:
{
double v___x_1783_; double v___x_1784_; double v___x_1785_; uint8_t v___x_1786_; 
v___x_1783_ = lean_unbox_float(v_snd_1730_);
v___x_1784_ = lean_unbox_float(v_fst_1729_);
v___x_1785_ = lean_float_sub(v___x_1783_, v___x_1784_);
v___x_1786_ = lean_float_decLt(v___y_1782_, v___x_1785_);
v___y_1750_ = v___x_1786_;
goto v___jp_1749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1797_, lean_object* v_collapsed_1798_, lean_object* v_tag_1799_, lean_object* v_opts_1800_, lean_object* v_clsEnabled_1801_, lean_object* v_oldTraces_1802_, lean_object* v_msg_1803_, lean_object* v_resStartStop_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_){
_start:
{
uint8_t v_collapsed_boxed_1810_; uint8_t v_clsEnabled_boxed_1811_; lean_object* v_res_1812_; 
v_collapsed_boxed_1810_ = lean_unbox(v_collapsed_1798_);
v_clsEnabled_boxed_1811_ = lean_unbox(v_clsEnabled_1801_);
v_res_1812_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1797_, v_collapsed_boxed_1810_, v_tag_1799_, v_opts_1800_, v_clsEnabled_boxed_1811_, v_oldTraces_1802_, v_msg_1803_, v_resStartStop_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec_ref(v_opts_1800_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_nat_dec_lt(v_a_1817_, v_upperBound_1813_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v_a_1817_);
lean_dec(v___x_1816_);
lean_dec(v___x_1815_);
lean_dec(v___x_1814_);
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v_b_1818_);
return v___x_1825_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_unsigned_to_nat(1u);
v___x_1828_ = lean_nat_add(v_a_1817_, v___x_1827_);
lean_dec(v_a_1817_);
lean_inc_n(v___x_1828_, 2);
lean_inc(v___x_1814_);
v___x_1829_ = lean_name_append_index_after(v___x_1814_, v___x_1828_);
lean_inc(v___x_1815_);
v___x_1830_ = lean_name_append_index_after(v___x_1815_, v___x_1828_);
lean_inc(v___x_1816_);
v___x_1831_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1829_, v___x_1816_, v___x_1830_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_dec_ref_known(v___x_1831_, 1);
v_a_1817_ = v___x_1828_;
v_b_1818_ = v___x_1826_;
goto _start;
}
else
{
lean_dec(v___x_1828_);
lean_dec(v___x_1816_);
lean_dec(v___x_1815_);
lean_dec(v___x_1814_);
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1833_, lean_object* v___x_1834_, lean_object* v___x_1835_, lean_object* v___x_1836_, lean_object* v_a_1837_, lean_object* v_b_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1833_, v___x_1834_, v___x_1835_, v___x_1836_, v_a_1837_, v_b_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v_upperBound_1833_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1855_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1856_ = l_Lean_Name_append(v___x_1855_, v___x_1854_);
return v___x_1856_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1857_; double v___x_1858_; 
v___x_1857_ = lean_unsigned_to_nat(1000000000u);
v___x_1858_ = lean_float_of_nat(v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_toCold_1865_; lean_object* v_options_1866_; lean_object* v_inheritedTraceOptions_1867_; uint8_t v_hasTrace_1868_; lean_object* v___x_1869_; 
v_toCold_1865_ = lean_ctor_get(v_a_1862_, 0);
v_options_1866_ = lean_ctor_get(v_toCold_1865_, 2);
v_inheritedTraceOptions_1867_ = lean_ctor_get(v_toCold_1865_, 11);
v_hasTrace_1868_ = lean_ctor_get_uint8(v_options_1866_, sizeof(void*)*1);
v___x_1869_ = lean_box(0);
if (v_hasTrace_1868_ == 0)
{
lean_object* v___x_1870_; 
lean_inc(v_indName_1859_);
v___x_1870_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1934_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1934_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1934_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
if (lean_obj_tag(v_a_1871_) == 5)
{
lean_object* v_val_1875_; uint8_t v_isRec_1876_; 
v_val_1875_ = lean_ctor_get(v_a_1871_, 0);
lean_inc_ref(v_val_1875_);
lean_dec_ref_known(v_a_1871_, 1);
v_isRec_1876_ = lean_ctor_get_uint8(v_val_1875_, sizeof(void*)*6);
if (v_isRec_1876_ == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1879_; 
lean_dec_ref(v_val_1875_);
lean_dec(v_indName_1859_);
v___x_1877_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1877_);
v___x_1879_ = v___x_1873_;
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
else
{
lean_object* v_toConstantVal_1881_; lean_object* v_numParams_1882_; lean_object* v_all_1883_; lean_object* v_numNested_1884_; lean_object* v_type_1885_; lean_object* v___x_1886_; 
lean_del_object(v___x_1873_);
v_toConstantVal_1881_ = lean_ctor_get(v_val_1875_, 0);
lean_inc_ref(v_toConstantVal_1881_);
v_numParams_1882_ = lean_ctor_get(v_val_1875_, 1);
lean_inc(v_numParams_1882_);
v_all_1883_ = lean_ctor_get(v_val_1875_, 3);
lean_inc(v_all_1883_);
v_numNested_1884_ = lean_ctor_get(v_val_1875_, 5);
lean_inc(v_numNested_1884_);
lean_dec_ref(v_val_1875_);
v_type_1885_ = lean_ctor_get(v_toConstantVal_1881_, 2);
lean_inc_ref(v_type_1885_);
lean_dec_ref(v_toConstantVal_1881_);
v___x_1886_ = l_Lean_Meta_isPropFormerType(v_type_1885_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1921_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_unbox(v_a_1887_);
lean_dec(v_a_1887_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_del_object(v___x_1889_);
lean_inc_n(v_indName_1859_, 2);
v___x_1892_ = l_Lean_mkRecName(v_indName_1859_);
v___x_1893_ = l_Lean_mkBelowName(v_indName_1859_);
lean_inc(v___x_1893_);
lean_inc(v_numParams_1882_);
lean_inc(v___x_1892_);
v___x_1894_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1892_, v_numParams_1882_, v___x_1893_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1915_; 
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1894_, 0);
lean_dec(v_unused_1916_);
v___x_1896_ = v___x_1894_;
v_isShared_1897_ = v_isSharedCheck_1915_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1915_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = l_List_get_x21Internal___redArg(v___x_1869_, v_all_1883_, v___x_1898_);
lean_dec(v_all_1883_);
v___x_1900_ = lean_name_eq(v___x_1899_, v_indName_1859_);
lean_dec(v_indName_1859_);
lean_dec(v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_dec(v___x_1893_);
lean_dec(v___x_1892_);
lean_dec(v_numNested_1884_);
lean_dec(v_numParams_1882_);
v___x_1901_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1901_);
v___x_1903_ = v___x_1896_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_del_object(v___x_1896_);
v___x_1905_ = lean_box(0);
v___x_1906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1884_, v___x_1892_, v___x_1893_, v_numParams_1882_, v___x_1898_, v___x_1905_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_numNested_1884_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1906_, 0);
lean_dec(v_unused_1914_);
v___x_1908_ = v___x_1906_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_dec(v___x_1906_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1905_);
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1905_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
return v___x_1906_;
}
}
}
}
else
{
lean_dec(v___x_1893_);
lean_dec(v___x_1892_);
lean_dec(v_numNested_1884_);
lean_dec(v_all_1883_);
lean_dec(v_numParams_1882_);
lean_dec(v_indName_1859_);
return v___x_1894_;
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec(v_numNested_1884_);
lean_dec(v_all_1883_);
lean_dec(v_numParams_1882_);
lean_dec(v_indName_1859_);
v___x_1917_ = lean_box(0);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1917_);
v___x_1919_ = v___x_1889_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_numNested_1884_);
lean_dec(v_all_1883_);
lean_dec(v_numParams_1882_);
lean_dec(v_indName_1859_);
v_a_1922_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1886_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1886_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
lean_dec(v_a_1871_);
lean_dec(v_indName_1859_);
v___x_1930_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1930_);
v___x_1932_ = v___x_1873_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec(v_indName_1859_);
v_a_1935_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1870_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1870_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_object* v___f_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_a_1951_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_a_1966_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v_a_1971_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v_a_1976_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_a_1988_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v_a_1993_; 
lean_inc(v_indName_1859_);
v___f_1943_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1943_, 0, v_indName_1859_);
v___x_1944_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1945_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1946_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1867_, v_options_1866_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = l_Lean_trace_profiler;
v___x_2059_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1866_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref(v___f_1943_);
lean_inc(v_indName_1859_);
v___x_2060_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2124_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2124_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2124_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
if (lean_obj_tag(v_a_2061_) == 5)
{
lean_object* v_val_2065_; uint8_t v_isRec_2066_; 
v_val_2065_ = lean_ctor_get(v_a_2061_, 0);
lean_inc_ref(v_val_2065_);
lean_dec_ref_known(v_a_2061_, 1);
v_isRec_2066_ = lean_ctor_get_uint8(v_val_2065_, sizeof(void*)*6);
if (v_isRec_2066_ == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
lean_dec_ref(v_val_2065_);
lean_dec(v_indName_1859_);
v___x_2067_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2067_);
v___x_2069_ = v___x_2063_;
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
else
{
lean_object* v_toConstantVal_2071_; lean_object* v_numParams_2072_; lean_object* v_all_2073_; lean_object* v_numNested_2074_; lean_object* v_type_2075_; lean_object* v___x_2076_; 
lean_del_object(v___x_2063_);
v_toConstantVal_2071_ = lean_ctor_get(v_val_2065_, 0);
lean_inc_ref(v_toConstantVal_2071_);
v_numParams_2072_ = lean_ctor_get(v_val_2065_, 1);
lean_inc(v_numParams_2072_);
v_all_2073_ = lean_ctor_get(v_val_2065_, 3);
lean_inc(v_all_2073_);
v_numNested_2074_ = lean_ctor_get(v_val_2065_, 5);
lean_inc(v_numNested_2074_);
lean_dec_ref(v_val_2065_);
v_type_2075_ = lean_ctor_get(v_toConstantVal_2071_, 2);
lean_inc_ref(v_type_2075_);
lean_dec_ref(v_toConstantVal_2071_);
v___x_2076_ = l_Lean_Meta_isPropFormerType(v_type_2075_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2111_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2079_ = v___x_2076_;
v_isShared_2080_ = v_isSharedCheck_2111_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2111_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_unbox(v_a_2077_);
lean_dec(v_a_2077_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_2079_);
lean_inc_n(v_indName_1859_, 2);
v___x_2082_ = l_Lean_mkRecName(v_indName_1859_);
v___x_2083_ = l_Lean_mkBelowName(v_indName_1859_);
lean_inc(v___x_2083_);
lean_inc(v_numParams_2072_);
lean_inc(v___x_2082_);
v___x_2084_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2082_, v_numParams_2072_, v___x_2083_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2105_; 
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v___x_2084_, 0);
lean_dec(v_unused_2106_);
v___x_2086_ = v___x_2084_;
v_isShared_2087_ = v_isSharedCheck_2105_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v___x_2084_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2105_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = l_List_get_x21Internal___redArg(v___x_1869_, v_all_2073_, v___x_2088_);
lean_dec(v_all_2073_);
v___x_2090_ = lean_name_eq(v___x_2089_, v_indName_1859_);
lean_dec(v_indName_1859_);
lean_dec(v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec(v___x_2083_);
lean_dec(v___x_2082_);
lean_dec(v_numNested_2074_);
lean_dec(v_numParams_2072_);
v___x_2091_ = lean_box(0);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2091_);
v___x_2093_ = v___x_2086_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_2086_);
v___x_2095_ = lean_box(0);
v___x_2096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2074_, v___x_2082_, v___x_2083_, v_numParams_2072_, v___x_2088_, v___x_2095_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_numNested_2074_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v___x_2096_, 0);
lean_dec(v_unused_2104_);
v___x_2098_ = v___x_2096_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_dec(v___x_2096_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2095_);
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2095_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
return v___x_2096_;
}
}
}
}
else
{
lean_dec(v___x_2083_);
lean_dec(v___x_2082_);
lean_dec(v_numNested_2074_);
lean_dec(v_all_2073_);
lean_dec(v_numParams_2072_);
lean_dec(v_indName_1859_);
return v___x_2084_;
}
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
lean_dec(v_numNested_2074_);
lean_dec(v_all_2073_);
lean_dec(v_numParams_2072_);
lean_dec(v_indName_1859_);
v___x_2107_ = lean_box(0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 0, v___x_2107_);
v___x_2109_ = v___x_2079_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v_numNested_2074_);
lean_dec(v_all_2073_);
lean_dec(v_numParams_2072_);
lean_dec(v_indName_1859_);
v_a_2112_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2076_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2076_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v_a_2061_);
lean_dec(v_indName_1859_);
v___x_2120_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2120_);
v___x_2122_ = v___x_2063_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_indName_1859_);
v_a_2125_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2060_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2060_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
goto v___jp_1995_;
}
}
else
{
goto v___jp_1995_;
}
v___jp_1948_:
{
lean_object* v___x_1952_; double v___x_1953_; double v___x_1954_; double v___x_1955_; double v___x_1956_; double v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1952_ = lean_io_mono_nanos_now();
v___x_1953_ = lean_float_of_nat(v___y_1950_);
v___x_1954_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1955_ = lean_float_div(v___x_1953_, v___x_1954_);
v___x_1956_ = lean_float_of_nat(v___x_1952_);
v___x_1957_ = lean_float_div(v___x_1956_, v___x_1954_);
v___x_1958_ = lean_box_float(v___x_1955_);
v___x_1959_ = lean_box_float(v___x_1957_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_a_1951_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1944_, v_hasTrace_1868_, v___x_1945_, v_options_1866_, v___x_1947_, v___y_1949_, v___f_1943_, v___x_1961_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1962_;
}
v___jp_1963_:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_a_1966_);
v___y_1949_ = v___y_1964_;
v___y_1950_ = v___y_1965_;
v_a_1951_ = v___x_1967_;
goto v___jp_1948_;
}
v___jp_1968_:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_a_1971_);
v___y_1949_ = v___y_1969_;
v___y_1950_ = v___y_1970_;
v_a_1951_ = v___x_1972_;
goto v___jp_1948_;
}
v___jp_1973_:
{
lean_object* v___x_1977_; double v___x_1978_; double v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1977_ = lean_io_get_num_heartbeats();
v___x_1978_ = lean_float_of_nat(v___y_1974_);
v___x_1979_ = lean_float_of_nat(v___x_1977_);
v___x_1980_ = lean_box_float(v___x_1978_);
v___x_1981_ = lean_box_float(v___x_1979_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_a_1976_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1944_, v_hasTrace_1868_, v___x_1945_, v_options_1866_, v___x_1947_, v___y_1975_, v___f_1943_, v___x_1983_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
return v___x_1984_;
}
v___jp_1985_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1988_);
v___y_1974_ = v___y_1986_;
v___y_1975_ = v___y_1987_;
v_a_1976_ = v___x_1989_;
goto v___jp_1973_;
}
v___jp_1990_:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_a_1993_);
v___y_1974_ = v___y_1991_;
v___y_1975_ = v___y_1992_;
v_a_1976_ = v___x_1994_;
goto v___jp_1973_;
}
v___jp_1995_:
{
lean_object* v___x_1996_; lean_object* v_a_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1996_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1863_);
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1999_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1866_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1859_);
v___x_2001_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
if (lean_obj_tag(v_a_2002_) == 5)
{
lean_object* v_val_2003_; uint8_t v_isRec_2004_; 
v_val_2003_ = lean_ctor_get(v_a_2002_, 0);
lean_inc_ref(v_val_2003_);
lean_dec_ref_known(v_a_2002_, 1);
v_isRec_2004_ = lean_ctor_get_uint8(v_val_2003_, sizeof(void*)*6);
if (v_isRec_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec_ref(v_val_2003_);
lean_dec(v_indName_1859_);
v___x_2005_ = lean_box(0);
v___y_1964_ = v_a_1997_;
v___y_1965_ = v___x_2000_;
v_a_1966_ = v___x_2005_;
goto v___jp_1963_;
}
else
{
lean_object* v_toConstantVal_2006_; lean_object* v_numParams_2007_; lean_object* v_all_2008_; lean_object* v_numNested_2009_; lean_object* v_type_2010_; lean_object* v___x_2011_; 
v_toConstantVal_2006_ = lean_ctor_get(v_val_2003_, 0);
lean_inc_ref(v_toConstantVal_2006_);
v_numParams_2007_ = lean_ctor_get(v_val_2003_, 1);
lean_inc(v_numParams_2007_);
v_all_2008_ = lean_ctor_get(v_val_2003_, 3);
lean_inc(v_all_2008_);
v_numNested_2009_ = lean_ctor_get(v_val_2003_, 5);
lean_inc(v_numNested_2009_);
lean_dec_ref(v_val_2003_);
v_type_2010_ = lean_ctor_get(v_toConstantVal_2006_, 2);
lean_inc_ref(v_type_2010_);
lean_dec_ref(v_toConstantVal_2006_);
v___x_2011_ = l_Lean_Meta_isPropFormerType(v_type_2010_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_unbox(v_a_2012_);
lean_dec(v_a_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_inc_n(v_indName_1859_, 2);
v___x_2014_ = l_Lean_mkRecName(v_indName_1859_);
v___x_2015_ = l_Lean_mkBelowName(v_indName_1859_);
lean_inc(v___x_2015_);
lean_inc(v_numParams_2007_);
lean_inc(v___x_2014_);
v___x_2016_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2014_, v_numParams_2007_, v___x_2015_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
lean_dec_ref_known(v___x_2016_, 1);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = l_List_get_x21Internal___redArg(v___x_1869_, v_all_2008_, v___x_2017_);
lean_dec(v_all_2008_);
v___x_2019_ = lean_name_eq(v___x_2018_, v_indName_1859_);
lean_dec(v_indName_1859_);
lean_dec(v___x_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v_numNested_2009_);
lean_dec(v_numParams_2007_);
v___x_2020_ = lean_box(0);
v___y_1964_ = v_a_1997_;
v___y_1965_ = v___x_2000_;
v_a_1966_ = v___x_2020_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_box(0);
v___x_2022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2009_, v___x_2014_, v___x_2015_, v_numParams_2007_, v___x_2017_, v___x_2021_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_numNested_2009_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_dec_ref_known(v___x_2022_, 1);
v___y_1964_ = v_a_1997_;
v___y_1965_ = v___x_2000_;
v_a_1966_ = v___x_2021_;
goto v___jp_1963_;
}
else
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___y_1969_ = v_a_1997_;
v___y_1970_ = v___x_2000_;
v_a_1971_ = v_a_2023_;
goto v___jp_1968_;
}
}
}
else
{
lean_object* v_a_2024_; 
lean_dec(v___x_2015_);
lean_dec(v___x_2014_);
lean_dec(v_numNested_2009_);
lean_dec(v_all_2008_);
lean_dec(v_numParams_2007_);
lean_dec(v_indName_1859_);
v_a_2024_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2016_, 1);
v___y_1969_ = v_a_1997_;
v___y_1970_ = v___x_2000_;
v_a_1971_ = v_a_2024_;
goto v___jp_1968_;
}
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_numNested_2009_);
lean_dec(v_all_2008_);
lean_dec(v_numParams_2007_);
lean_dec(v_indName_1859_);
v___x_2025_ = lean_box(0);
v___y_1964_ = v_a_1997_;
v___y_1965_ = v___x_2000_;
v_a_1966_ = v___x_2025_;
goto v___jp_1963_;
}
}
else
{
lean_object* v_a_2026_; 
lean_dec(v_numNested_2009_);
lean_dec(v_all_2008_);
lean_dec(v_numParams_2007_);
lean_dec(v_indName_1859_);
v_a_2026_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1969_ = v_a_1997_;
v___y_1970_ = v___x_2000_;
v_a_1971_ = v_a_2026_;
goto v___jp_1968_;
}
}
}
else
{
lean_object* v___x_2027_; 
lean_dec(v_a_2002_);
lean_dec(v_indName_1859_);
v___x_2027_ = lean_box(0);
v___y_1964_ = v_a_1997_;
v___y_1965_ = v___x_2000_;
v_a_1966_ = v___x_2027_;
goto v___jp_1963_;
}
}
else
{
lean_object* v_a_2028_; 
lean_dec(v_indName_1859_);
v_a_2028_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2001_, 1);
v___y_1969_ = v_a_1997_;
v___y_1970_ = v___x_2000_;
v_a_1971_ = v_a_2028_;
goto v___jp_1968_;
}
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1859_);
v___x_2030_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
if (lean_obj_tag(v_a_2031_) == 5)
{
lean_object* v_val_2032_; uint8_t v_isRec_2033_; 
v_val_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc_ref(v_val_2032_);
lean_dec_ref_known(v_a_2031_, 1);
v_isRec_2033_ = lean_ctor_get_uint8(v_val_2032_, sizeof(void*)*6);
if (v_isRec_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec_ref(v_val_2032_);
lean_dec(v_indName_1859_);
v___x_2034_ = lean_box(0);
v___y_1986_ = v___x_2029_;
v___y_1987_ = v_a_1997_;
v_a_1988_ = v___x_2034_;
goto v___jp_1985_;
}
else
{
lean_object* v_toConstantVal_2035_; lean_object* v_numParams_2036_; lean_object* v_all_2037_; lean_object* v_numNested_2038_; lean_object* v_type_2039_; lean_object* v___x_2040_; 
v_toConstantVal_2035_ = lean_ctor_get(v_val_2032_, 0);
lean_inc_ref(v_toConstantVal_2035_);
v_numParams_2036_ = lean_ctor_get(v_val_2032_, 1);
lean_inc(v_numParams_2036_);
v_all_2037_ = lean_ctor_get(v_val_2032_, 3);
lean_inc(v_all_2037_);
v_numNested_2038_ = lean_ctor_get(v_val_2032_, 5);
lean_inc(v_numNested_2038_);
lean_dec_ref(v_val_2032_);
v_type_2039_ = lean_ctor_get(v_toConstantVal_2035_, 2);
lean_inc_ref(v_type_2039_);
lean_dec_ref(v_toConstantVal_2035_);
v___x_2040_ = l_Lean_Meta_isPropFormerType(v_type_2039_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; uint8_t v___x_2042_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = lean_unbox(v_a_2041_);
lean_dec(v_a_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_inc_n(v_indName_1859_, 2);
v___x_2043_ = l_Lean_mkRecName(v_indName_1859_);
v___x_2044_ = l_Lean_mkBelowName(v_indName_1859_);
lean_inc(v___x_2044_);
lean_inc(v_numParams_2036_);
lean_inc(v___x_2043_);
v___x_2045_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2043_, v_numParams_2036_, v___x_2044_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
lean_dec_ref_known(v___x_2045_, 1);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_List_get_x21Internal___redArg(v___x_1869_, v_all_2037_, v___x_2046_);
lean_dec(v_all_2037_);
v___x_2048_ = lean_name_eq(v___x_2047_, v_indName_1859_);
lean_dec(v_indName_1859_);
lean_dec(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; 
lean_dec(v___x_2044_);
lean_dec(v___x_2043_);
lean_dec(v_numNested_2038_);
lean_dec(v_numParams_2036_);
v___x_2049_ = lean_box(0);
v___y_1986_ = v___x_2029_;
v___y_1987_ = v_a_1997_;
v_a_1988_ = v___x_2049_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_box(0);
v___x_2051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2038_, v___x_2043_, v___x_2044_, v_numParams_2036_, v___x_2046_, v___x_2050_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_numNested_2038_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_dec_ref_known(v___x_2051_, 1);
v___y_1986_ = v___x_2029_;
v___y_1987_ = v_a_1997_;
v_a_1988_ = v___x_2050_;
goto v___jp_1985_;
}
else
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___y_1991_ = v___x_2029_;
v___y_1992_ = v_a_1997_;
v_a_1993_ = v_a_2052_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v_a_2053_; 
lean_dec(v___x_2044_);
lean_dec(v___x_2043_);
lean_dec(v_numNested_2038_);
lean_dec(v_all_2037_);
lean_dec(v_numParams_2036_);
lean_dec(v_indName_1859_);
v_a_2053_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2045_, 1);
v___y_1991_ = v___x_2029_;
v___y_1992_ = v_a_1997_;
v_a_1993_ = v_a_2053_;
goto v___jp_1990_;
}
}
else
{
lean_object* v___x_2054_; 
lean_dec(v_numNested_2038_);
lean_dec(v_all_2037_);
lean_dec(v_numParams_2036_);
lean_dec(v_indName_1859_);
v___x_2054_ = lean_box(0);
v___y_1986_ = v___x_2029_;
v___y_1987_ = v_a_1997_;
v_a_1988_ = v___x_2054_;
goto v___jp_1985_;
}
}
else
{
lean_object* v_a_2055_; 
lean_dec(v_numNested_2038_);
lean_dec(v_all_2037_);
lean_dec(v_numParams_2036_);
lean_dec(v_indName_1859_);
v_a_2055_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2040_, 1);
v___y_1991_ = v___x_2029_;
v___y_1992_ = v_a_1997_;
v_a_1993_ = v_a_2055_;
goto v___jp_1990_;
}
}
}
else
{
lean_object* v___x_2056_; 
lean_dec(v_a_2031_);
lean_dec(v_indName_1859_);
v___x_2056_ = lean_box(0);
v___y_1986_ = v___x_2029_;
v___y_1987_ = v_a_1997_;
v_a_1988_ = v___x_2056_;
goto v___jp_1985_;
}
}
else
{
lean_object* v_a_2057_; 
lean_dec(v_indName_1859_);
v_a_2057_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2030_, 1);
v___y_1991_ = v___x_2029_;
v___y_1992_ = v_a_1997_;
v_a_1993_ = v_a_2057_;
goto v___jp_1990_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_mkBelow(v_indName_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2140_, lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v___x_2143_, lean_object* v_inst_2144_, lean_object* v_R_2145_, lean_object* v_a_2146_, lean_object* v_b_2147_, lean_object* v_c_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2140_, v___x_2141_, v___x_2142_, v___x_2143_, v_a_2146_, v_b_2147_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2155_, lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v___x_2158_, lean_object* v_inst_2159_, lean_object* v_R_2160_, lean_object* v_a_2161_, lean_object* v_b_2162_, lean_object* v_c_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2155_, v___x_2156_, v___x_2157_, v___x_2158_, v_inst_2159_, v_R_2160_, v_a_2161_, v_b_2162_, v_c_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_upperBound_2155_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2170_, lean_object* v_x_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2171_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_x_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2178_, v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
if (lean_obj_tag(v_a_2186_) == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = l_List_reverse___redArg(v_a_2187_);
return v___x_2188_;
}
else
{
lean_object* v_head_2189_; lean_object* v_tail_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2199_; 
v_head_2189_ = lean_ctor_get(v_a_2186_, 0);
v_tail_2190_ = lean_ctor_get(v_a_2186_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2186_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2192_ = v_a_2186_;
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_tail_2190_);
lean_inc(v_head_2189_);
lean_dec(v_a_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2199_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = l_Lean_MessageData_ofExpr(v_head_2189_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v_a_2187_);
lean_ctor_set(v___x_2192_, 0, v___x_2194_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_a_2187_);
v___x_2196_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2186_ = v_tail_2190_;
v_a_2187_ = v___x_2196_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2200_, lean_object* v_v_2201_, lean_object* v_i_2202_){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_array_get_size(v_xs_2200_);
v___x_2204_ = lean_nat_dec_lt(v_i_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; 
lean_dec(v_i_2202_);
v___x_2205_ = lean_box(0);
return v___x_2205_;
}
else
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = lean_array_fget_borrowed(v_xs_2200_, v_i_2202_);
v___x_2207_ = lean_expr_eqv(v___x_2206_, v_v_2201_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_unsigned_to_nat(1u);
v___x_2209_ = lean_nat_add(v_i_2202_, v___x_2208_);
lean_dec(v_i_2202_);
v_i_2202_ = v___x_2209_;
goto _start;
}
else
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_i_2202_);
return v___x_2211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2212_, lean_object* v_v_2213_, lean_object* v_i_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2212_, v_v_2213_, v_i_2214_);
lean_dec_ref(v_v_2213_);
lean_dec_ref(v_xs_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2216_, lean_object* v_v_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2216_, v_v_2217_, v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2220_, lean_object* v_v_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2220_, v_v_2221_);
lean_dec_ref(v_v_2221_);
lean_dec_ref(v_xs_2220_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2223_, lean_object* v_v_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2223_, v_v_2224_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_box(0);
return v___x_2226_;
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
v_val_2227_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2225_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_val_2227_);
lean_dec(v___x_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_val_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2235_, lean_object* v_v_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2235_, v_v_2236_);
lean_dec_ref(v_v_2236_);
lean_dec_ref(v_xs_2235_);
return v_res_2237_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2244_, lean_object* v_prods_2245_, lean_object* v_motives_2246_, lean_object* v_fs_2247_, lean_object* v_minor__type_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
if (lean_obj_tag(v_x_2249_) == 5)
{
lean_object* v_fn_2257_; lean_object* v_arg_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v_fn_2257_ = lean_ctor_get(v_x_2249_, 0);
lean_inc_ref(v_fn_2257_);
v_arg_2258_ = lean_ctor_get(v_x_2249_, 1);
lean_inc_ref(v_arg_2258_);
lean_dec_ref_known(v_x_2249_, 2);
v___x_2259_ = lean_array_set(v_x_2250_, v_x_2251_, v_arg_2258_);
v___x_2260_ = lean_unsigned_to_nat(1u);
v___x_2261_ = lean_nat_sub(v_x_2251_, v___x_2260_);
lean_dec(v_x_2251_);
v_x_2249_ = v_fn_2257_;
v_x_2250_ = v___x_2259_;
v_x_2251_ = v___x_2261_;
goto _start;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_dec(v_x_2251_);
v___x_2263_ = l_Lean_instInhabitedExpr;
v___x_2264_ = l_Lean_Meta_PProdN_mk(v_rlvl_2244_, v_prods_2245_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2246_, v_x_2249_);
lean_dec_ref(v_x_2249_);
if (lean_obj_tag(v___x_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec_ref(v_minor__type_2248_);
lean_dec_ref(v_motives_2246_);
v_val_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = lean_array_get_borrowed(v___x_2263_, v_fs_2247_, v_val_2267_);
lean_dec(v_val_2267_);
lean_inc(v_a_2265_);
v___x_2269_ = lean_array_push(v_x_2250_, v_a_2265_);
lean_inc(v___x_2268_);
v___x_2270_ = l_Lean_mkAppN(v___x_2268_, v___x_2269_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = l_Lean_Meta_mkPProdMk(v___x_2270_, v_a_2265_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v___x_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_x_2250_);
v___x_2272_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2273_ = l_Lean_MessageData_ofExpr(v_minor__type_2248_);
v___x_2274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2272_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2274_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_array_to_list(v_motives_2246_);
v___x_2278_ = lean_box(0);
v___x_2279_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2277_, v___x_2278_);
v___x_2280_ = l_Lean_MessageData_ofList(v___x_2279_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2276_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2281_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2282_;
}
}
else
{
lean_dec_ref(v_x_2250_);
lean_dec_ref(v_x_2249_);
lean_dec_ref(v_minor__type_2248_);
lean_dec_ref(v_motives_2246_);
return v___x_2264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2283_, lean_object* v_prods_2284_, lean_object* v_motives_2285_, lean_object* v_fs_2286_, lean_object* v_minor__type_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2283_, v_prods_2284_, v_motives_2285_, v_fs_2286_, v_minor__type_2287_, v_x_2288_, v_x_2289_, v_x_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec_ref(v_fs_2286_);
return v_res_2296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2297_; lean_object* v_dummy_2298_; 
v___x_2297_ = lean_box(0);
v_dummy_2298_ = l_Lean_Expr_sort___override(v___x_2297_);
return v_dummy_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2299_, lean_object* v_head_2300_, lean_object* v_belows_2301_, lean_object* v_prods_2302_, lean_object* v_rlvl_2303_, lean_object* v_fs_2304_, lean_object* v_minor__type_2305_, lean_object* v_tail_2306_, lean_object* v_arg__args_2307_, lean_object* v_arg__type_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2299_, v_head_2300_, v_belows_2301_, v_prods_2302_, v_rlvl_2303_, v_fs_2304_, v_minor__type_2305_, v_tail_2306_, v_arg__args_2307_, v_arg__type_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_arg__args_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2315_, lean_object* v_motives_2316_, lean_object* v_belows_2317_, lean_object* v_fs_2318_, lean_object* v_minor__type_2319_, lean_object* v_prods_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
if (lean_obj_tag(v_a_2321_) == 0)
{
lean_object* v_dummy_2327_; lean_object* v_nargs_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec_ref(v_belows_2317_);
v_dummy_2327_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2328_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2319_);
lean_inc(v_nargs_2328_);
v___x_2329_ = lean_mk_array(v_nargs_2328_, v_dummy_2327_);
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_sub(v_nargs_2328_, v___x_2330_);
lean_dec(v_nargs_2328_);
lean_inc_ref(v_minor__type_2319_);
v___x_2332_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2315_, v_prods_2320_, v_motives_2316_, v_fs_2318_, v_minor__type_2319_, v_minor__type_2319_, v___x_2329_, v___x_2331_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
lean_dec_ref(v_fs_2318_);
return v___x_2332_;
}
else
{
lean_object* v_head_2333_; lean_object* v_tail_2334_; lean_object* v___f_2335_; lean_object* v___x_2336_; 
v_head_2333_ = lean_ctor_get(v_a_2321_, 0);
lean_inc_n(v_head_2333_, 2);
v_tail_2334_ = lean_ctor_get(v_a_2321_, 1);
lean_inc(v_tail_2334_);
lean_dec_ref_known(v_a_2321_, 2);
v___f_2335_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2335_, 0, v_motives_2316_);
lean_closure_set(v___f_2335_, 1, v_head_2333_);
lean_closure_set(v___f_2335_, 2, v_belows_2317_);
lean_closure_set(v___f_2335_, 3, v_prods_2320_);
lean_closure_set(v___f_2335_, 4, v_rlvl_2315_);
lean_closure_set(v___f_2335_, 5, v_fs_2318_);
lean_closure_set(v___f_2335_, 6, v_minor__type_2319_);
lean_closure_set(v___f_2335_, 7, v_tail_2334_);
lean_inc(v_a_2325_);
lean_inc_ref(v_a_2324_);
lean_inc(v_a_2323_);
lean_inc_ref(v_a_2322_);
v___x_2336_ = lean_infer_type(v_head_2333_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = 0;
v___x_2339_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2337_, v___f_2335_, v___x_2338_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_);
return v___x_2339_;
}
else
{
lean_dec_ref(v___f_2335_);
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2340_, lean_object* v_rlvl_2341_, lean_object* v_motives_2342_, lean_object* v_belows_2343_, lean_object* v_fs_2344_, lean_object* v_minor__type_2345_, lean_object* v_tail_2346_, uint8_t v___x_2347_, uint8_t v___x_2348_, uint8_t v___x_2349_, lean_object* v_arg_x27_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_inc_ref(v_arg_x27_2350_);
v___x_2356_ = lean_array_push(v_prods_2340_, v_arg_x27_2350_);
v___x_2357_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2341_, v_motives_2342_, v_belows_2343_, v_fs_2344_, v_minor__type_2345_, v___x_2356_, v_tail_2346_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v___x_2357_, 1);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_mk_empty_array_with_capacity(v___x_2359_);
v___x_2361_ = lean_array_push(v___x_2360_, v_arg_x27_2350_);
v___x_2362_ = l_Lean_Meta_mkLambdaFVars(v___x_2361_, v_a_2358_, v___x_2347_, v___x_2348_, v___x_2347_, v___x_2348_, v___x_2349_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec_ref(v___x_2361_);
return v___x_2362_;
}
else
{
lean_dec_ref(v_arg_x27_2350_);
return v___x_2357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2363_, lean_object* v_rlvl_2364_, lean_object* v_motives_2365_, lean_object* v_belows_2366_, lean_object* v_fs_2367_, lean_object* v_minor__type_2368_, lean_object* v_tail_2369_, lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v_arg_x27_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v___x_1689__boxed_2379_; uint8_t v___x_1690__boxed_2380_; uint8_t v___x_1691__boxed_2381_; lean_object* v_res_2382_; 
v___x_1689__boxed_2379_ = lean_unbox(v___x_2370_);
v___x_1690__boxed_2380_ = lean_unbox(v___x_2371_);
v___x_1691__boxed_2381_ = lean_unbox(v___x_2372_);
v_res_2382_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2363_, v_rlvl_2364_, v_motives_2365_, v_belows_2366_, v_fs_2367_, v_minor__type_2368_, v_tail_2369_, v___x_1689__boxed_2379_, v___x_1690__boxed_2380_, v___x_1691__boxed_2381_, v_arg_x27_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2383_, lean_object* v_head_2384_, lean_object* v_belows_2385_, lean_object* v_arg__type_2386_, lean_object* v_prods_2387_, lean_object* v_rlvl_2388_, lean_object* v_fs_2389_, lean_object* v_minor__type_2390_, lean_object* v_tail_2391_, lean_object* v_arg__args_2392_, lean_object* v_x_2393_, lean_object* v_x_2394_, lean_object* v_x_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
if (lean_obj_tag(v_x_2393_) == 5)
{
lean_object* v_fn_2401_; lean_object* v_arg_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_fn_2401_ = lean_ctor_get(v_x_2393_, 0);
lean_inc_ref(v_fn_2401_);
v_arg_2402_ = lean_ctor_get(v_x_2393_, 1);
lean_inc_ref(v_arg_2402_);
lean_dec_ref_known(v_x_2393_, 2);
v___x_2403_ = lean_array_set(v_x_2394_, v_x_2395_, v_arg_2402_);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = lean_nat_sub(v_x_2395_, v___x_2404_);
lean_dec(v_x_2395_);
v_x_2393_ = v_fn_2401_;
v_x_2394_ = v___x_2403_;
v_x_2395_ = v___x_2405_;
goto _start;
}
else
{
lean_object* v___x_2407_; 
lean_dec(v_x_2395_);
v___x_2407_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2383_, v_x_2393_);
lean_dec_ref(v_x_2393_);
if (lean_obj_tag(v___x_2407_) == 1)
{
lean_object* v_val_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_val_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_instInhabitedExpr;
v___x_2410_ = l_Lean_Expr_fvarId_x21(v_head_2384_);
lean_dec_ref(v_head_2384_);
v___x_2411_ = l_Lean_FVarId_getUserName___redArg(v___x_2410_, v___y_2396_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2413_ = lean_array_get_borrowed(v___x_2409_, v_belows_2385_, v_val_2408_);
lean_dec(v_val_2408_);
lean_inc(v___x_2413_);
v___x_2414_ = l_Lean_mkAppN(v___x_2413_, v_x_2394_);
lean_dec_ref(v_x_2394_);
v___x_2415_ = l_Lean_Meta_mkPProd(v_arg__type_2386_, v___x_2414_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; uint8_t v___x_2417_; uint8_t v___x_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___f_2423_; lean_object* v___x_2424_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = 0;
v___x_2418_ = 1;
v___x_2419_ = 1;
v___x_2420_ = lean_box(v___x_2417_);
v___x_2421_ = lean_box(v___x_2418_);
v___x_2422_ = lean_box(v___x_2419_);
v___f_2423_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2423_, 0, v_prods_2387_);
lean_closure_set(v___f_2423_, 1, v_rlvl_2388_);
lean_closure_set(v___f_2423_, 2, v_motives_2383_);
lean_closure_set(v___f_2423_, 3, v_belows_2385_);
lean_closure_set(v___f_2423_, 4, v_fs_2389_);
lean_closure_set(v___f_2423_, 5, v_minor__type_2390_);
lean_closure_set(v___f_2423_, 6, v_tail_2391_);
lean_closure_set(v___f_2423_, 7, v___x_2420_);
lean_closure_set(v___f_2423_, 8, v___x_2421_);
lean_closure_set(v___f_2423_, 9, v___x_2422_);
v___x_2424_ = l_Lean_Meta_mkForallFVars(v_arg__args_2392_, v_a_2416_, v___x_2417_, v___x_2418_, v___x_2418_, v___x_2419_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2412_, v_a_2425_, v___f_2423_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v___x_2426_;
}
else
{
lean_dec_ref(v___f_2423_);
lean_dec(v_a_2412_);
return v___x_2424_;
}
}
else
{
lean_dec(v_a_2412_);
lean_dec(v_tail_2391_);
lean_dec_ref(v_minor__type_2390_);
lean_dec_ref(v_fs_2389_);
lean_dec(v_rlvl_2388_);
lean_dec_ref(v_prods_2387_);
lean_dec_ref(v_belows_2385_);
lean_dec_ref(v_motives_2383_);
return v___x_2415_;
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_val_2408_);
lean_dec_ref(v_x_2394_);
lean_dec(v_tail_2391_);
lean_dec_ref(v_minor__type_2390_);
lean_dec_ref(v_fs_2389_);
lean_dec(v_rlvl_2388_);
lean_dec_ref(v_prods_2387_);
lean_dec_ref(v_arg__type_2386_);
lean_dec_ref(v_belows_2385_);
lean_dec_ref(v_motives_2383_);
v_a_2427_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2411_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2411_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v___x_2435_; 
lean_dec(v___x_2407_);
lean_dec_ref(v_x_2394_);
lean_dec_ref(v_arg__type_2386_);
v___x_2435_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2388_, v_motives_2383_, v_belows_2385_, v_fs_2389_, v_minor__type_2390_, v_prods_2387_, v_tail_2391_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; uint8_t v___x_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_mk_empty_array_with_capacity(v___x_2437_);
v___x_2439_ = lean_array_push(v___x_2438_, v_head_2384_);
v___x_2440_ = 0;
v___x_2441_ = 1;
v___x_2442_ = 1;
v___x_2443_ = l_Lean_Meta_mkLambdaFVars(v___x_2439_, v_a_2436_, v___x_2440_, v___x_2441_, v___x_2440_, v___x_2441_, v___x_2442_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec_ref(v___x_2439_);
return v___x_2443_;
}
else
{
lean_dec_ref(v_head_2384_);
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2444_, lean_object* v_head_2445_, lean_object* v_belows_2446_, lean_object* v_prods_2447_, lean_object* v_rlvl_2448_, lean_object* v_fs_2449_, lean_object* v_minor__type_2450_, lean_object* v_tail_2451_, lean_object* v_arg__args_2452_, lean_object* v_arg__type_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_dummy_2459_; lean_object* v_nargs_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_dummy_2459_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2460_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2453_);
lean_inc(v_nargs_2460_);
v___x_2461_ = lean_mk_array(v_nargs_2460_, v_dummy_2459_);
v___x_2462_ = lean_unsigned_to_nat(1u);
v___x_2463_ = lean_nat_sub(v_nargs_2460_, v___x_2462_);
lean_dec(v_nargs_2460_);
lean_inc_ref(v_arg__type_2453_);
v___x_2464_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2444_, v_head_2445_, v_belows_2446_, v_arg__type_2453_, v_prods_2447_, v_rlvl_2448_, v_fs_2449_, v_minor__type_2450_, v_tail_2451_, v_arg__args_2452_, v_arg__type_2453_, v___x_2461_, v___x_2463_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2465_, lean_object* v_motives_2466_, lean_object* v_belows_2467_, lean_object* v_fs_2468_, lean_object* v_minor__type_2469_, lean_object* v_prods_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2465_, v_motives_2466_, v_belows_2467_, v_fs_2468_, v_minor__type_2469_, v_prods_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2478_ = _args[0];
lean_object* v_head_2479_ = _args[1];
lean_object* v_belows_2480_ = _args[2];
lean_object* v_arg__type_2481_ = _args[3];
lean_object* v_prods_2482_ = _args[4];
lean_object* v_rlvl_2483_ = _args[5];
lean_object* v_fs_2484_ = _args[6];
lean_object* v_minor__type_2485_ = _args[7];
lean_object* v_tail_2486_ = _args[8];
lean_object* v_arg__args_2487_ = _args[9];
lean_object* v_x_2488_ = _args[10];
lean_object* v_x_2489_ = _args[11];
lean_object* v_x_2490_ = _args[12];
lean_object* v___y_2491_ = _args[13];
lean_object* v___y_2492_ = _args[14];
lean_object* v___y_2493_ = _args[15];
lean_object* v___y_2494_ = _args[16];
lean_object* v___y_2495_ = _args[17];
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2478_, v_head_2479_, v_belows_2480_, v_arg__type_2481_, v_prods_2482_, v_rlvl_2483_, v_fs_2484_, v_minor__type_2485_, v_tail_2486_, v_arg__args_2487_, v_x_2488_, v_x_2489_, v_x_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v_arg__args_2487_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2497_, lean_object* v_motives_2498_, lean_object* v_belows_2499_, lean_object* v_fs_2500_, lean_object* v_minor__args_2501_, lean_object* v_minor__type_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2508_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2509_ = lean_array_to_list(v_minor__args_2501_);
v___x_2510_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2497_, v_motives_2498_, v_belows_2499_, v_fs_2500_, v_minor__type_2502_, v___x_2508_, v___x_2509_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2511_, lean_object* v_motives_2512_, lean_object* v_belows_2513_, lean_object* v_fs_2514_, lean_object* v_minor__args_2515_, lean_object* v_minor__type_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2511_, v_motives_2512_, v_belows_2513_, v_fs_2514_, v_minor__args_2515_, v_minor__type_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2523_, lean_object* v_motives_2524_, lean_object* v_belows_2525_, lean_object* v_fs_2526_, lean_object* v_minorType_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v___f_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; 
v___f_2533_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2533_, 0, v_rlvl_2523_);
lean_closure_set(v___f_2533_, 1, v_motives_2524_);
lean_closure_set(v___f_2533_, 2, v_belows_2525_);
lean_closure_set(v___f_2533_, 3, v_fs_2526_);
v___x_2534_ = 0;
v___x_2535_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2527_, v___f_2533_, v___x_2534_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2536_, lean_object* v_motives_2537_, lean_object* v_belows_2538_, lean_object* v_fs_2539_, lean_object* v_minorType_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2536_, v_motives_2537_, v_belows_2538_, v_fs_2539_, v_minorType_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___f_2553_; lean_object* v___x_29418__overap_2554_; lean_object* v___x_2555_; 
v___f_2553_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_29418__overap_2554_ = lean_panic_fn_borrowed(v___f_2553_, v_msg_2547_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
v___x_2555_ = lean_apply_5(v___x_29418__overap_2554_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, lean_box(0));
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = l_Lean_Expr_hasMVar(v_e_2563_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_e_2563_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v_mctx_2569_; lean_object* v___x_2570_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2573_; lean_object* v_cache_2574_; lean_object* v_zetaDeltaFVarIds_2575_; lean_object* v_postponed_2576_; lean_object* v_diag_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2586_; 
v___x_2568_ = lean_st_ref_get(v___y_2564_);
v_mctx_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc_ref(v_mctx_2569_);
lean_dec(v___x_2568_);
v___x_2570_ = l_Lean_instantiateMVarsCore(v_mctx_2569_, v_e_2563_);
v_fst_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_fst_2571_);
v_snd_2572_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2572_);
lean_dec_ref(v___x_2570_);
v___x_2573_ = lean_st_ref_take(v___y_2564_);
v_cache_2574_ = lean_ctor_get(v___x_2573_, 1);
v_zetaDeltaFVarIds_2575_ = lean_ctor_get(v___x_2573_, 2);
v_postponed_2576_ = lean_ctor_get(v___x_2573_, 3);
v_diag_2577_ = lean_ctor_get(v___x_2573_, 4);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2573_, 0);
lean_dec(v_unused_2587_);
v___x_2579_ = v___x_2573_;
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_diag_2577_);
lean_inc(v_postponed_2576_);
lean_inc(v_zetaDeltaFVarIds_2575_);
lean_inc(v_cache_2574_);
lean_dec(v___x_2573_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_snd_2572_);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_snd_2572_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_cache_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_zetaDeltaFVarIds_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_postponed_2576_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_diag_2577_);
v___x_2582_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_st_ref_put(v___y_2564_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_fst_2571_);
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2588_, v___y_2589_);
lean_dec(v___y_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2592_, v___y_2594_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v_env_2610_; lean_object* v_toConstantVal_2611_; lean_object* v_value_2612_; lean_object* v_all_2613_; lean_object* v_type_2620_; uint8_t v___x_2621_; 
v___x_2609_ = lean_st_ref_get(v___y_2607_);
v_env_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc_ref_n(v_env_2610_, 2);
lean_dec(v___x_2609_);
v_toConstantVal_2611_ = lean_ctor_get(v_thm_2606_, 0);
v_value_2612_ = lean_ctor_get(v_thm_2606_, 1);
v_all_2613_ = lean_ctor_get(v_thm_2606_, 2);
v_type_2620_ = lean_ctor_get(v_toConstantVal_2611_, 2);
v___x_2621_ = l_Lean_Environment_hasUnsafe(v_env_2610_, v_type_2620_);
if (v___x_2621_ == 0)
{
uint8_t v___x_2622_; 
v___x_2622_ = l_Lean_Environment_hasUnsafe(v_env_2610_, v_value_2612_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_thm_2606_);
v___x_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
return v___x_2624_;
}
else
{
lean_inc(v_all_2613_);
lean_inc_ref(v_value_2612_);
lean_inc_ref(v_toConstantVal_2611_);
lean_dec_ref(v_thm_2606_);
goto v___jp_2614_;
}
}
else
{
lean_inc(v_all_2613_);
lean_inc_ref(v_value_2612_);
lean_inc_ref(v_toConstantVal_2611_);
lean_dec_ref(v_env_2610_);
lean_dec_ref(v_thm_2606_);
goto v___jp_2614_;
}
v___jp_2614_:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2615_ = lean_box(0);
v___x_2616_ = 0;
v___x_2617_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2617_, 0, v_toConstantVal_2611_);
lean_ctor_set(v___x_2617_, 1, v_value_2612_);
lean_ctor_set(v___x_2617_, 2, v___x_2615_);
lean_ctor_set(v___x_2617_, 3, v_all_2613_);
lean_ctor_set_uint8(v___x_2617_, sizeof(void*)*4, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2625_, v___y_2626_);
lean_dec(v___y_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2629_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2644_, lean_object* v___x_2645_, lean_object* v___x_2646_, lean_object* v_all_2647_, lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v___y_2653_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_array_get_size(v_all_2647_);
v___x_2658_ = lean_nat_dec_lt(v_x_2651_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2659_ = lean_array_get_borrowed(v___x_2648_, v_all_2647_, v___x_2649_);
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2661_ = lean_nat_sub(v_x_2651_, v___x_2657_);
v___x_2662_ = lean_nat_add(v___x_2661_, v___x_2650_);
lean_dec(v___x_2661_);
v___x_2663_ = l_Nat_reprFast(v___x_2662_);
v___x_2664_ = lean_string_append(v___x_2660_, v___x_2663_);
lean_dec_ref(v___x_2663_);
lean_inc(v___x_2659_);
v___x_2665_ = l_Lean_Name_str___override(v___x_2659_, v___x_2664_);
v___y_2653_ = v___x_2665_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_array_fget_borrowed(v_all_2647_, v_x_2651_);
lean_inc(v___x_2666_);
v___x_2667_ = l_Lean_mkBelowName(v___x_2666_);
v___y_2653_ = v___x_2667_;
goto v___jp_2652_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = l_Lean_Expr_const___override(v___y_2653_, v___x_2644_);
v___x_2655_ = l_Array_append___redArg(v___x_2645_, v___x_2646_);
v___x_2656_ = l_Lean_mkAppN(v___x_2654_, v___x_2655_);
lean_dec_ref(v___x_2655_);
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2668_, lean_object* v___x_2669_, lean_object* v___x_2670_, lean_object* v_all_2671_, lean_object* v___x_2672_, lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v_x_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2668_, v___x_2669_, v___x_2670_, v_all_2671_, v___x_2672_, v___x_2673_, v___x_2674_, v_x_2675_);
lean_dec(v_x_2675_);
lean_dec(v___x_2674_);
lean_dec(v___x_2673_);
lean_dec(v___x_2672_);
lean_dec_ref(v_all_2671_);
lean_dec_ref(v___x_2670_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2677_, lean_object* v___x_2678_, lean_object* v___x_2679_, lean_object* v_fs_2680_, lean_object* v_as_2681_, size_t v_sz_2682_, size_t v_i_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_usize_dec_lt(v_i_2683_, v_sz_2682_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; 
lean_dec_ref(v_fs_2680_);
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2678_);
lean_dec(v___x_2677_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_b_2684_);
return v___x_2691_;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_array_uget_borrowed(v_as_2681_, v_i_2683_);
lean_inc(v___y_2688_);
lean_inc_ref(v___y_2687_);
lean_inc(v___y_2686_);
lean_inc_ref(v___y_2685_);
lean_inc(v_a_2692_);
v___x_2693_ = lean_infer_type(v_a_2692_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
lean_inc_ref(v_fs_2680_);
lean_inc_ref(v___x_2679_);
lean_inc_ref(v___x_2678_);
lean_inc(v___x_2677_);
v___x_2695_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2677_, v___x_2678_, v___x_2679_, v_fs_2680_, v_a_2694_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; size_t v___x_2698_; size_t v___x_2699_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = l_Lean_Expr_app___override(v_b_2684_, v_a_2696_);
v___x_2698_ = ((size_t)1ULL);
v___x_2699_ = lean_usize_add(v_i_2683_, v___x_2698_);
v_i_2683_ = v___x_2699_;
v_b_2684_ = v___x_2697_;
goto _start;
}
else
{
lean_dec_ref(v_b_2684_);
lean_dec_ref(v_fs_2680_);
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2678_);
lean_dec(v___x_2677_);
return v___x_2695_;
}
}
else
{
lean_dec_ref(v_b_2684_);
lean_dec_ref(v_fs_2680_);
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2678_);
lean_dec(v___x_2677_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2701_, lean_object* v___x_2702_, lean_object* v___x_2703_, lean_object* v_fs_2704_, lean_object* v_as_2705_, lean_object* v_sz_2706_, lean_object* v_i_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
size_t v_sz_boxed_2714_; size_t v_i_boxed_2715_; lean_object* v_res_2716_; 
v_sz_boxed_2714_ = lean_unbox_usize(v_sz_2706_);
lean_dec(v_sz_2706_);
v_i_boxed_2715_ = lean_unbox_usize(v_i_2707_);
lean_dec(v_i_2707_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2701_, v___x_2702_, v___x_2703_, v_fs_2704_, v_as_2705_, v_sz_boxed_2714_, v_i_boxed_2715_, v_b_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_as_2705_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2717_, lean_object* v___x_2718_, uint8_t v___x_2719_, lean_object* v_targs_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = l_Lean_mkAppN(v_a_2717_, v_targs_2720_);
v___x_2728_ = l_Lean_mkAppN(v___x_2718_, v_targs_2720_);
v___x_2729_ = l_Lean_Meta_mkPProd(v___x_2727_, v___x_2728_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; uint8_t v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = 0;
v___x_2732_ = 1;
v___x_2733_ = l_Lean_Meta_mkLambdaFVars(v_targs_2720_, v_a_2730_, v___x_2731_, v___x_2719_, v___x_2731_, v___x_2719_, v___x_2732_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2733_;
}
else
{
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2734_, lean_object* v___x_2735_, lean_object* v___x_2736_, lean_object* v_targs_2737_, lean_object* v_x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
uint8_t v___x_32708__boxed_2744_; lean_object* v_res_2745_; 
v___x_32708__boxed_2744_ = lean_unbox(v___x_2736_);
v_res_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2734_, v___x_2735_, v___x_32708__boxed_2744_, v_targs_2737_, v_x_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec_ref(v_x_2738_);
lean_dec_ref(v_targs_2737_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v_as_2748_, size_t v_sz_2749_, size_t v_i_2750_, lean_object* v_b_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_usize_dec_lt(v_i_2750_, v_sz_2749_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_b_2751_);
return v___x_2758_;
}
else
{
lean_object* v_snd_2759_; lean_object* v_fst_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2817_; 
v_snd_2759_ = lean_ctor_get(v_b_2751_, 1);
v_fst_2760_ = lean_ctor_get(v_b_2751_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_b_2751_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2762_ = v_b_2751_;
v_isShared_2763_ = v_isSharedCheck_2817_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_snd_2759_);
lean_inc(v_fst_2760_);
lean_dec(v_b_2751_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2817_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v_array_2764_; lean_object* v_start_2765_; lean_object* v_stop_2766_; uint8_t v___x_2767_; 
v_array_2764_ = lean_ctor_get(v_snd_2759_, 0);
v_start_2765_ = lean_ctor_get(v_snd_2759_, 1);
v_stop_2766_ = lean_ctor_get(v_snd_2759_, 2);
v___x_2767_ = lean_nat_dec_lt(v_start_2765_, v_stop_2766_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2769_; 
if (v_isShared_2763_ == 0)
{
v___x_2769_ = v___x_2762_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_fst_2760_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_snd_2759_);
v___x_2769_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
}
else
{
lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2813_; 
lean_inc(v_stop_2766_);
lean_inc(v_start_2765_);
lean_inc_ref(v_array_2764_);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_snd_2759_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; lean_object* v_unused_2815_; lean_object* v_unused_2816_; 
v_unused_2814_ = lean_ctor_get(v_snd_2759_, 2);
lean_dec(v_unused_2814_);
v_unused_2815_ = lean_ctor_get(v_snd_2759_, 1);
lean_dec(v_unused_2815_);
v_unused_2816_ = lean_ctor_get(v_snd_2759_, 0);
lean_dec(v_unused_2816_);
v___x_2773_ = v_snd_2759_;
v_isShared_2774_ = v_isSharedCheck_2813_;
goto v_resetjp_2772_;
}
else
{
lean_dec(v_snd_2759_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2813_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint8_t v___x_2775_; lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___f_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2775_ = lean_nat_dec_lt(v___x_2746_, v___x_2747_);
v_a_2776_ = lean_array_uget_borrowed(v_as_2748_, v_i_2750_);
v___x_2777_ = lean_array_fget_borrowed(v_array_2764_, v_start_2765_);
v___x_2778_ = lean_box(v___x_2775_);
lean_inc(v___x_2777_);
lean_inc(v_a_2776_);
v___f_2779_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2779_, 0, v_a_2776_);
lean_closure_set(v___f_2779_, 1, v___x_2777_);
lean_closure_set(v___f_2779_, 2, v___x_2778_);
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_add(v_start_2765_, v___x_2780_);
lean_dec(v_start_2765_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v___x_2781_);
v___x_2783_ = v___x_2773_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_array_2764_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_stop_2766_);
v___x_2783_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2784_; 
lean_inc(v___y_2755_);
lean_inc_ref(v___y_2754_);
lean_inc(v___y_2753_);
lean_inc_ref(v___y_2752_);
lean_inc(v_a_2776_);
v___x_2784_ = lean_infer_type(v_a_2776_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = 0;
v___x_2787_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2785_, v___f_2779_, v___x_2786_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = l_Lean_Expr_app___override(v_fst_2760_, v_a_2788_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 1, v___x_2783_);
lean_ctor_set(v___x_2762_, 0, v___x_2789_);
v___x_2791_ = v___x_2762_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2783_);
v___x_2791_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
size_t v___x_2792_; size_t v___x_2793_; 
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_add(v_i_2750_, v___x_2792_);
v_i_2750_ = v___x_2793_;
v_b_2751_ = v___x_2791_;
goto _start;
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v___x_2783_);
lean_del_object(v___x_2762_);
lean_dec(v_fst_2760_);
v_a_2796_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2787_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2787_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v___x_2783_);
lean_dec_ref(v___f_2779_);
lean_del_object(v___x_2762_);
lean_dec(v_fst_2760_);
v_a_2804_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2784_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2784_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_as_2820_, lean_object* v_sz_2821_, lean_object* v_i_2822_, lean_object* v_b_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
size_t v_sz_boxed_2829_; size_t v_i_boxed_2830_; lean_object* v_res_2831_; 
v_sz_boxed_2829_ = lean_unbox_usize(v_sz_2821_);
lean_dec(v_sz_2821_);
v_i_boxed_2830_ = lean_unbox_usize(v_i_2822_);
lean_dec(v_i_2822_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2818_, v___x_2819_, v_as_2820_, v_sz_boxed_2829_, v_i_boxed_2830_, v_b_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_as_2820_);
lean_dec(v___x_2819_);
lean_dec(v___x_2818_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2832_, size_t v_sz_2833_, size_t v_i_2834_, lean_object* v_b_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
uint8_t v___x_2841_; 
v___x_2841_ = lean_usize_dec_lt(v_i_2834_, v_sz_2833_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2842_, 0, v_b_2835_);
return v___x_2842_;
}
else
{
lean_object* v_a_2843_; lean_object* v_toInductionSubgoal_2844_; lean_object* v_mvarId_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_a_2843_ = lean_array_uget_borrowed(v_as_2832_, v_i_2834_);
v_toInductionSubgoal_2844_ = lean_ctor_get(v_a_2843_, 0);
v_mvarId_2845_ = lean_ctor_get(v_toInductionSubgoal_2844_, 0);
v___x_2846_ = 0;
v___x_2847_ = lean_box(0);
lean_inc(v_mvarId_2845_);
v___x_2848_ = l_Lean_MVarId_refl(v_mvarId_2845_, v___x_2846_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2848_) == 0)
{
size_t v___x_2849_; size_t v___x_2850_; 
lean_dec_ref_known(v___x_2848_, 1);
v___x_2849_ = ((size_t)1ULL);
v___x_2850_ = lean_usize_add(v_i_2834_, v___x_2849_);
v_i_2834_ = v___x_2850_;
v_b_2835_ = v___x_2847_;
goto _start;
}
else
{
return v___x_2848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2852_, lean_object* v_sz_2853_, lean_object* v_i_2854_, lean_object* v_b_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
size_t v_sz_boxed_2861_; size_t v_i_boxed_2862_; lean_object* v_res_2863_; 
v_sz_boxed_2861_ = lean_unbox_usize(v_sz_2853_);
lean_dec(v_sz_2853_);
v_i_boxed_2862_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2852_, v_sz_boxed_2861_, v_i_boxed_2862_, v_b_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec_ref(v_as_2852_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2864_, lean_object* v_tail_2865_, lean_object* v_recName_2866_, lean_object* v___x_2867_, lean_object* v___x_2868_, lean_object* v___x_2869_, lean_object* v___x_2870_, lean_object* v___x_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v_val_2878_, uint8_t v___x_2879_, lean_object* v_brecOnGoName_2880_, lean_object* v_levelParams_2881_, lean_object* v___x_2882_, lean_object* v___x_2883_, lean_object* v_brecOnName_2884_, lean_object* v_brecOnEqName_2885_, lean_object* v_fs_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; size_t v_sz_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
lean_inc(v___x_2864_);
v___x_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2864_);
lean_ctor_set(v___x_2892_, 1, v_tail_2865_);
v___x_2893_ = l_Lean_Expr_const___override(v_recName_2866_, v___x_2892_);
v___x_2894_ = l_Lean_mkAppN(v___x_2893_, v___x_2867_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
lean_ctor_set(v___x_2895_, 1, v___x_2868_);
v_sz_2896_ = lean_array_size(v___x_2869_);
v___x_2897_ = ((size_t)0ULL);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2870_, v___x_2871_, v___x_2869_, v_sz_2896_, v___x_2897_, v___x_2895_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_fst_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_3269_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v_fst_2900_ = lean_ctor_get(v_a_2899_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_a_2899_);
if (v_isSharedCheck_3269_ == 0)
{
lean_object* v_unused_3270_; 
v_unused_3270_ = lean_ctor_get(v_a_2899_, 1);
lean_dec(v_unused_3270_);
v___x_2902_ = v_a_2899_;
v_isShared_2903_ = v_isSharedCheck_3269_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_fst_2900_);
lean_dec(v_a_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_3269_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
size_t v_sz_2904_; lean_object* v___x_2905_; 
v_sz_2904_ = lean_array_size(v___x_2872_);
lean_inc_ref(v_fs_2886_);
lean_inc_ref(v___x_2873_);
lean_inc_ref(v___x_2869_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2864_, v___x_2869_, v___x_2873_, v_fs_2886_, v___x_2872_, v_sz_2904_, v___x_2897_, v_fst_2900_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_mkAppN(v_a_2906_, v___x_2874_);
lean_inc_ref_n(v___x_2875_, 3);
v___x_2908_ = l_Lean_Expr_app___override(v___x_2907_, v___x_2875_);
v___x_2909_ = l_Array_append___redArg(v___x_2867_, v___x_2869_);
v___x_2910_ = l_Array_append___redArg(v___x_2909_, v___x_2874_);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2876_);
v___x_2912_ = lean_array_push(v___x_2911_, v___x_2875_);
v___x_2913_ = l_Array_append___redArg(v___x_2910_, v___x_2912_);
lean_dec_ref(v___x_2912_);
v___x_2914_ = l_Array_append___redArg(v___x_2913_, v_fs_2886_);
v___x_2915_ = lean_array_get(v___x_2877_, v___x_2869_, v_val_2878_);
lean_dec_ref(v___x_2869_);
v___x_2916_ = lean_array_push(v___x_2874_, v___x_2875_);
v___x_2917_ = l_Lean_mkAppN(v___x_2915_, v___x_2916_);
v___x_2918_ = lean_array_get(v___x_2877_, v___x_2873_, v_val_2878_);
lean_dec_ref(v___x_2873_);
v___x_2919_ = l_Lean_mkAppN(v___x_2918_, v___x_2916_);
lean_inc_ref(v___x_2917_);
v___x_2920_ = l_Lean_Meta_mkPProd(v___x_2917_, v___x_2919_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; uint8_t v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
v___x_2922_ = 0;
v___x_2923_ = 1;
v___x_2924_ = l_Lean_Meta_mkForallFVars(v___x_2914_, v_a_2921_, v___x_2922_, v___x_2879_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2926_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___x_2924_, 1);
v___x_2926_ = l_Lean_Meta_mkLambdaFVars(v___x_2914_, v___x_2908_, v___x_2922_, v___x_2879_, v___x_2922_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_3236_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = lean_box(1);
lean_inc(v_levelParams_2881_);
lean_inc(v_brecOnGoName_2880_);
v___x_2929_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2880_, v_levelParams_2881_, v_a_2925_, v_a_2927_, v___x_2928_, v___y_2890_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_3236_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_3236_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
lean_inc(v_a_2930_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set_tag(v___x_2932_, 1);
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_3235_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_addDecl(v___x_2935_, v___x_2922_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_toConstantVal_2937_; lean_object* v_name_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref_known(v___x_2936_, 1);
v_toConstantVal_2937_ = lean_ctor_get(v_a_2930_, 0);
lean_inc_ref(v_toConstantVal_2937_);
lean_dec(v_a_2930_);
v_name_2938_ = lean_ctor_get(v_toConstantVal_2937_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_toConstantVal_2937_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; 
v_unused_3233_ = lean_ctor_get(v_toConstantVal_2937_, 2);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_toConstantVal_2937_, 1);
lean_dec(v_unused_3234_);
v___x_2940_ = v_toConstantVal_2937_;
v_isShared_2941_ = v_isSharedCheck_3232_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_name_2938_);
lean_dec(v_toConstantVal_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3232_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_env_2944_; lean_object* v_nextMacroScope_2945_; lean_object* v_ngen_2946_; lean_object* v_auxDeclNGen_2947_; lean_object* v_traceState_2948_; lean_object* v_recordedDeps_2949_; lean_object* v_messages_2950_; lean_object* v_infoState_2951_; lean_object* v_snapshotTasks_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3230_; 
lean_inc(v_name_2938_);
v___x_2942_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2938_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec_ref(v___x_2942_);
v___x_2943_ = lean_st_ref_take(v___y_2890_);
v_env_2944_ = lean_ctor_get(v___x_2943_, 0);
v_nextMacroScope_2945_ = lean_ctor_get(v___x_2943_, 1);
v_ngen_2946_ = lean_ctor_get(v___x_2943_, 2);
v_auxDeclNGen_2947_ = lean_ctor_get(v___x_2943_, 3);
v_traceState_2948_ = lean_ctor_get(v___x_2943_, 4);
v_recordedDeps_2949_ = lean_ctor_get(v___x_2943_, 6);
v_messages_2950_ = lean_ctor_get(v___x_2943_, 7);
v_infoState_2951_ = lean_ctor_get(v___x_2943_, 8);
v_snapshotTasks_2952_ = lean_ctor_get(v___x_2943_, 9);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_2943_, 5);
lean_dec(v_unused_3231_);
v___x_2954_ = v___x_2943_;
v_isShared_2955_ = v_isSharedCheck_3230_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_snapshotTasks_2952_);
lean_inc(v_infoState_2951_);
lean_inc(v_messages_2950_);
lean_inc(v_recordedDeps_2949_);
lean_inc(v_traceState_2948_);
lean_inc(v_auxDeclNGen_2947_);
lean_inc(v_ngen_2946_);
lean_inc(v_nextMacroScope_2945_);
lean_inc(v_env_2944_);
lean_dec(v___x_2943_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3230_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2956_ = l_Lean_addProtected(v_env_2944_, v_name_2938_);
v___x_2957_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_2958_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 5, v___x_2958_);
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2960_ = v___x_2954_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_nextMacroScope_2945_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_ngen_2946_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_auxDeclNGen_2947_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_traceState_2948_);
lean_ctor_set(v_reuseFailAlloc_3229_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3229_, 6, v_recordedDeps_2949_);
lean_ctor_set(v_reuseFailAlloc_3229_, 7, v_messages_2950_);
lean_ctor_set(v_reuseFailAlloc_3229_, 8, v_infoState_2951_);
lean_ctor_set(v_reuseFailAlloc_3229_, 9, v_snapshotTasks_2952_);
v___x_2960_ = v_reuseFailAlloc_3229_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v_mctx_2963_; lean_object* v_zetaDeltaFVarIds_2964_; lean_object* v_postponed_2965_; lean_object* v_diag_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3227_; 
v___x_2961_ = lean_st_ref_put(v___y_2890_, v___x_2960_);
v___x_2962_ = lean_st_ref_take(v___y_2888_);
v_mctx_2963_ = lean_ctor_get(v___x_2962_, 0);
v_zetaDeltaFVarIds_2964_ = lean_ctor_get(v___x_2962_, 2);
v_postponed_2965_ = lean_ctor_get(v___x_2962_, 3);
v_diag_2966_ = lean_ctor_get(v___x_2962_, 4);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_2962_, 1);
lean_dec(v_unused_3228_);
v___x_2968_ = v___x_2962_;
v_isShared_2969_ = v_isSharedCheck_3227_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_diag_2966_);
lean_inc(v_postponed_2965_);
lean_inc(v_zetaDeltaFVarIds_2964_);
lean_inc(v_mctx_2963_);
lean_dec(v___x_2962_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3227_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2970_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
v___x_2971_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
lean_inc(v___x_2882_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 2, v___x_2882_);
lean_ctor_set(v___x_2940_, 1, v___x_2957_);
lean_ctor_set(v___x_2940_, 0, v___x_2957_);
v___x_2973_ = v___x_2940_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v___x_2882_);
v___x_2973_ = v_reuseFailAlloc_3226_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2976_; 
v___x_2974_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2970_);
lean_ctor_set(v___x_2974_, 1, v___x_2957_);
lean_ctor_set(v___x_2974_, 2, v___x_2971_);
lean_ctor_set(v___x_2974_, 3, v___x_2957_);
lean_ctor_set(v___x_2974_, 4, v___x_2957_);
lean_ctor_set(v___x_2974_, 5, v___x_2957_);
lean_ctor_set(v___x_2974_, 6, v___x_2973_);
lean_inc_ref(v___x_2974_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_2974_);
v___x_2976_ = v___x_2968_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_mctx_2963_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_zetaDeltaFVarIds_2964_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_postponed_2965_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_diag_2966_);
v___x_2976_ = v_reuseFailAlloc_3225_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2977_ = lean_st_ref_put(v___y_2888_, v___x_2976_);
lean_inc(v___x_2883_);
v___x_2978_ = l_Lean_Expr_const___override(v_brecOnGoName_2880_, v___x_2883_);
v___x_2979_ = l_Lean_mkAppN(v___x_2978_, v___x_2914_);
lean_inc_ref(v___x_2979_);
v___x_2980_ = l_Lean_Meta_mkPProdFstM(v___x_2979_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l_Lean_Meta_mkLambdaFVars(v___x_2914_, v_a_2981_, v___x_2922_, v___x_2879_, v___x_2922_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = l_Lean_Meta_mkForallFVars(v___x_2914_, v___x_2917_, v___x_2922_, v___x_2879_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3200_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
lean_inc(v_levelParams_2881_);
v___x_2986_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2884_, v_levelParams_2881_, v_a_2985_, v_a_2983_, v___x_2928_, v___y_2890_);
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_3200_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3200_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
lean_inc(v_a_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 1);
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_3199_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_addDecl(v___x_2992_, v___x_2922_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_toConstantVal_2994_; lean_object* v_name_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3196_; 
lean_dec_ref_known(v___x_2993_, 1);
v_toConstantVal_2994_ = lean_ctor_get(v_a_2987_, 0);
lean_inc_ref(v_toConstantVal_2994_);
lean_dec(v_a_2987_);
v_name_2995_ = lean_ctor_get(v_toConstantVal_2994_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_toConstantVal_2994_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; lean_object* v_unused_3198_; 
v_unused_3197_ = lean_ctor_get(v_toConstantVal_2994_, 2);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v_toConstantVal_2994_, 1);
lean_dec(v_unused_3198_);
v___x_2997_ = v_toConstantVal_2994_;
v_isShared_2998_ = v_isSharedCheck_3196_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_name_2995_);
lean_dec(v_toConstantVal_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3196_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_env_3001_; lean_object* v_nextMacroScope_3002_; lean_object* v_ngen_3003_; lean_object* v_auxDeclNGen_3004_; lean_object* v_traceState_3005_; lean_object* v_recordedDeps_3006_; lean_object* v_messages_3007_; lean_object* v_infoState_3008_; lean_object* v_snapshotTasks_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3194_; 
lean_inc(v_name_2995_);
v___x_2999_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2995_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec_ref(v___x_2999_);
v___x_3000_ = lean_st_ref_take(v___y_2890_);
v_env_3001_ = lean_ctor_get(v___x_3000_, 0);
v_nextMacroScope_3002_ = lean_ctor_get(v___x_3000_, 1);
v_ngen_3003_ = lean_ctor_get(v___x_3000_, 2);
v_auxDeclNGen_3004_ = lean_ctor_get(v___x_3000_, 3);
v_traceState_3005_ = lean_ctor_get(v___x_3000_, 4);
v_recordedDeps_3006_ = lean_ctor_get(v___x_3000_, 6);
v_messages_3007_ = lean_ctor_get(v___x_3000_, 7);
v_infoState_3008_ = lean_ctor_get(v___x_3000_, 8);
v_snapshotTasks_3009_ = lean_ctor_get(v___x_3000_, 9);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3194_ == 0)
{
lean_object* v_unused_3195_; 
v_unused_3195_ = lean_ctor_get(v___x_3000_, 5);
lean_dec(v_unused_3195_);
v___x_3011_ = v___x_3000_;
v_isShared_3012_ = v_isSharedCheck_3194_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snapshotTasks_3009_);
lean_inc(v_infoState_3008_);
lean_inc(v_messages_3007_);
lean_inc(v_recordedDeps_3006_);
lean_inc(v_traceState_3005_);
lean_inc(v_auxDeclNGen_3004_);
lean_inc(v_ngen_3003_);
lean_inc(v_nextMacroScope_3002_);
lean_inc(v_env_3001_);
lean_dec(v___x_3000_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3194_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
lean_inc(v_name_2995_);
v___x_3013_ = l_Lean_markAuxRecursor(v_env_3001_, v_name_2995_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 5, v___x_2958_);
lean_ctor_set(v___x_3011_, 0, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_nextMacroScope_3002_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_ngen_3003_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_auxDeclNGen_3004_);
lean_ctor_set(v_reuseFailAlloc_3193_, 4, v_traceState_3005_);
lean_ctor_set(v_reuseFailAlloc_3193_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3193_, 6, v_recordedDeps_3006_);
lean_ctor_set(v_reuseFailAlloc_3193_, 7, v_messages_3007_);
lean_ctor_set(v_reuseFailAlloc_3193_, 8, v_infoState_3008_);
lean_ctor_set(v_reuseFailAlloc_3193_, 9, v_snapshotTasks_3009_);
v___x_3015_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v_mctx_3018_; lean_object* v_zetaDeltaFVarIds_3019_; lean_object* v_postponed_3020_; lean_object* v_diag_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3191_; 
v___x_3016_ = lean_st_ref_put(v___y_2890_, v___x_3015_);
v___x_3017_ = lean_st_ref_take(v___y_2888_);
v_mctx_3018_ = lean_ctor_get(v___x_3017_, 0);
v_zetaDeltaFVarIds_3019_ = lean_ctor_get(v___x_3017_, 2);
v_postponed_3020_ = lean_ctor_get(v___x_3017_, 3);
v_diag_3021_ = lean_ctor_get(v___x_3017_, 4);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3191_ == 0)
{
lean_object* v_unused_3192_; 
v_unused_3192_ = lean_ctor_get(v___x_3017_, 1);
lean_dec(v_unused_3192_);
v___x_3023_ = v___x_3017_;
v_isShared_3024_ = v_isSharedCheck_3191_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_diag_3021_);
lean_inc(v_postponed_3020_);
lean_inc(v_zetaDeltaFVarIds_3019_);
lean_inc(v_mctx_3018_);
lean_dec(v___x_3017_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3191_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
lean_inc_ref(v___x_2974_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_2974_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_mctx_3018_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3190_, 2, v_zetaDeltaFVarIds_3019_);
lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_postponed_3020_);
lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_diag_3021_);
v___x_3026_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v_env_3029_; lean_object* v_nextMacroScope_3030_; lean_object* v_ngen_3031_; lean_object* v_auxDeclNGen_3032_; lean_object* v_traceState_3033_; lean_object* v_recordedDeps_3034_; lean_object* v_messages_3035_; lean_object* v_infoState_3036_; lean_object* v_snapshotTasks_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3188_; 
v___x_3027_ = lean_st_ref_put(v___y_2888_, v___x_3026_);
v___x_3028_ = lean_st_ref_take(v___y_2890_);
v_env_3029_ = lean_ctor_get(v___x_3028_, 0);
v_nextMacroScope_3030_ = lean_ctor_get(v___x_3028_, 1);
v_ngen_3031_ = lean_ctor_get(v___x_3028_, 2);
v_auxDeclNGen_3032_ = lean_ctor_get(v___x_3028_, 3);
v_traceState_3033_ = lean_ctor_get(v___x_3028_, 4);
v_recordedDeps_3034_ = lean_ctor_get(v___x_3028_, 6);
v_messages_3035_ = lean_ctor_get(v___x_3028_, 7);
v_infoState_3036_ = lean_ctor_get(v___x_3028_, 8);
v_snapshotTasks_3037_ = lean_ctor_get(v___x_3028_, 9);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3028_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; 
v_unused_3189_ = lean_ctor_get(v___x_3028_, 5);
lean_dec(v_unused_3189_);
v___x_3039_ = v___x_3028_;
v_isShared_3040_ = v_isSharedCheck_3188_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_snapshotTasks_3037_);
lean_inc(v_infoState_3036_);
lean_inc(v_messages_3035_);
lean_inc(v_recordedDeps_3034_);
lean_inc(v_traceState_3033_);
lean_inc(v_auxDeclNGen_3032_);
lean_inc(v_ngen_3031_);
lean_inc(v_nextMacroScope_3030_);
lean_inc(v_env_3029_);
lean_dec(v___x_3028_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3188_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_inc(v_name_2995_);
v___x_3041_ = l_Lean_addProtected(v_env_3029_, v_name_2995_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 5, v___x_2958_);
lean_ctor_set(v___x_3039_, 0, v___x_3041_);
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_nextMacroScope_3030_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_ngen_3031_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v_auxDeclNGen_3032_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_traceState_3033_);
lean_ctor_set(v_reuseFailAlloc_3187_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3187_, 6, v_recordedDeps_3034_);
lean_ctor_set(v_reuseFailAlloc_3187_, 7, v_messages_3035_);
lean_ctor_set(v_reuseFailAlloc_3187_, 8, v_infoState_3036_);
lean_ctor_set(v_reuseFailAlloc_3187_, 9, v_snapshotTasks_3037_);
v___x_3043_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v_mctx_3046_; lean_object* v_zetaDeltaFVarIds_3047_; lean_object* v_postponed_3048_; lean_object* v_diag_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3185_; 
v___x_3044_ = lean_st_ref_put(v___y_2890_, v___x_3043_);
v___x_3045_ = lean_st_ref_take(v___y_2888_);
v_mctx_3046_ = lean_ctor_get(v___x_3045_, 0);
v_zetaDeltaFVarIds_3047_ = lean_ctor_get(v___x_3045_, 2);
v_postponed_3048_ = lean_ctor_get(v___x_3045_, 3);
v_diag_3049_ = lean_ctor_get(v___x_3045_, 4);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; 
v_unused_3186_ = lean_ctor_get(v___x_3045_, 1);
lean_dec(v_unused_3186_);
v___x_3051_ = v___x_3045_;
v_isShared_3052_ = v_isSharedCheck_3185_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_diag_3049_);
lean_inc(v_postponed_3048_);
lean_inc(v_zetaDeltaFVarIds_3047_);
lean_inc(v_mctx_3046_);
lean_dec(v___x_3045_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3185_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
lean_inc_ref(v___x_2974_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v___x_2974_);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_mctx_3046_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_zetaDeltaFVarIds_3047_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_postponed_3048_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v_diag_3049_);
v___x_3054_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3055_ = lean_st_ref_put(v___y_2888_, v___x_3054_);
v___x_3056_ = l_Lean_Expr_const___override(v_name_2995_, v___x_2883_);
v___x_3057_ = l_Lean_mkAppN(v___x_3056_, v___x_2914_);
v___x_3058_ = lean_array_get(v___x_2877_, v_fs_2886_, v_val_2878_);
lean_dec_ref(v_fs_2886_);
v___x_3059_ = l_Lean_mkAppN(v___x_3058_, v___x_2916_);
lean_dec_ref(v___x_2916_);
v___x_3060_ = l_Lean_Meta_mkPProdSndM(v___x_2979_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_Expr_app___override(v___x_3059_, v_a_3061_);
v___x_3063_ = l_Lean_Meta_mkEq(v___x_3057_, v___x_3062_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc_n(v_a_3064_, 2);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = lean_box(0);
v___x_3066_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3064_, v___x_3065_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
v___x_3068_ = l_Lean_Expr_mvarId_x21(v_a_3067_);
v___x_3069_ = l_Lean_Expr_fvarId_x21(v___x_2875_);
lean_dec_ref(v___x_2875_);
v___x_3070_ = lean_mk_empty_array_with_capacity(v___x_2882_);
lean_dec(v___x_2882_);
v___x_3071_ = lean_box(0);
v___x_3072_ = l_Lean_MVarId_cases(v___x_3068_, v___x_3069_, v___x_3070_, v___x_2922_, v___x_3071_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; size_t v_sz_3075_; lean_object* v___x_3076_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = lean_box(0);
v_sz_3075_ = lean_array_size(v_a_3073_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3073_, v_sz_3075_, v___x_2897_, v___x_3074_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec(v_a_3073_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v___x_3077_; lean_object* v_a_3078_; lean_object* v___x_3079_; 
lean_dec_ref_known(v___x_3076_, 1);
v___x_3077_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3067_, v___y_2888_);
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref(v___x_3077_);
v___x_3079_ = l_Lean_Meta_mkForallFVars(v___x_2914_, v_a_3064_, v___x_2922_, v___x_2879_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l_Lean_Meta_mkLambdaFVars(v___x_2914_, v_a_3078_, v___x_2922_, v___x_2879_, v___x_2922_, v___x_2879_, v___x_2923_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
lean_dec_ref(v___x_2914_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3084_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
lean_inc(v_brecOnEqName_2885_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 2, v_a_3080_);
lean_ctor_set(v___x_2997_, 1, v_levelParams_2881_);
lean_ctor_set(v___x_2997_, 0, v_brecOnEqName_2885_);
v___x_3084_ = v___x_2997_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_brecOnEqName_2885_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_levelParams_2881_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_a_3080_);
v___x_3084_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
v___x_3085_ = lean_box(0);
lean_inc(v_brecOnEqName_2885_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set_tag(v___x_2902_, 1);
lean_ctor_set(v___x_2902_, 1, v___x_3085_);
lean_ctor_set(v___x_2902_, 0, v_brecOnEqName_2885_);
v___x_3087_ = v___x_2902_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_brecOnEqName_2885_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v_a_3090_; lean_object* v___x_3091_; 
v___x_3088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3084_);
lean_ctor_set(v___x_3088_, 1, v_a_3082_);
lean_ctor_set(v___x_3088_, 2, v___x_3087_);
v___x_3089_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3088_, v___y_2890_);
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref(v___x_3089_);
v___x_3091_ = l_Lean_addDecl(v_a_3090_, v___x_2922_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3132_; 
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_3091_, 0);
lean_dec(v_unused_3133_);
v___x_3093_ = v___x_3091_;
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
else
{
lean_dec(v___x_3091_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v_env_3096_; lean_object* v_nextMacroScope_3097_; lean_object* v_ngen_3098_; lean_object* v_auxDeclNGen_3099_; lean_object* v_traceState_3100_; lean_object* v_recordedDeps_3101_; lean_object* v_messages_3102_; lean_object* v_infoState_3103_; lean_object* v_snapshotTasks_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3130_; 
v___x_3095_ = lean_st_ref_take(v___y_2890_);
v_env_3096_ = lean_ctor_get(v___x_3095_, 0);
v_nextMacroScope_3097_ = lean_ctor_get(v___x_3095_, 1);
v_ngen_3098_ = lean_ctor_get(v___x_3095_, 2);
v_auxDeclNGen_3099_ = lean_ctor_get(v___x_3095_, 3);
v_traceState_3100_ = lean_ctor_get(v___x_3095_, 4);
v_recordedDeps_3101_ = lean_ctor_get(v___x_3095_, 6);
v_messages_3102_ = lean_ctor_get(v___x_3095_, 7);
v_infoState_3103_ = lean_ctor_get(v___x_3095_, 8);
v_snapshotTasks_3104_ = lean_ctor_get(v___x_3095_, 9);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_3095_, 5);
lean_dec(v_unused_3131_);
v___x_3106_ = v___x_3095_;
v_isShared_3107_ = v_isSharedCheck_3130_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_snapshotTasks_3104_);
lean_inc(v_infoState_3103_);
lean_inc(v_messages_3102_);
lean_inc(v_recordedDeps_3101_);
lean_inc(v_traceState_3100_);
lean_inc(v_auxDeclNGen_3099_);
lean_inc(v_ngen_3098_);
lean_inc(v_nextMacroScope_3097_);
lean_inc(v_env_3096_);
lean_dec(v___x_3095_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3130_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3108_ = l_Lean_addProtected(v_env_3096_, v_brecOnEqName_2885_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 5, v___x_2958_);
lean_ctor_set(v___x_3106_, 0, v___x_3108_);
v___x_3110_ = v___x_3106_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_nextMacroScope_3097_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_ngen_3098_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v_auxDeclNGen_3099_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v_traceState_3100_);
lean_ctor_set(v_reuseFailAlloc_3129_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3129_, 6, v_recordedDeps_3101_);
lean_ctor_set(v_reuseFailAlloc_3129_, 7, v_messages_3102_);
lean_ctor_set(v_reuseFailAlloc_3129_, 8, v_infoState_3103_);
lean_ctor_set(v_reuseFailAlloc_3129_, 9, v_snapshotTasks_3104_);
v___x_3110_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v_mctx_3113_; lean_object* v_zetaDeltaFVarIds_3114_; lean_object* v_postponed_3115_; lean_object* v_diag_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3127_; 
v___x_3111_ = lean_st_ref_put(v___y_2890_, v___x_3110_);
v___x_3112_ = lean_st_ref_take(v___y_2888_);
v_mctx_3113_ = lean_ctor_get(v___x_3112_, 0);
v_zetaDeltaFVarIds_3114_ = lean_ctor_get(v___x_3112_, 2);
v_postponed_3115_ = lean_ctor_get(v___x_3112_, 3);
v_diag_3116_ = lean_ctor_get(v___x_3112_, 4);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3112_, 1);
lean_dec(v_unused_3128_);
v___x_3118_ = v___x_3112_;
v_isShared_3119_ = v_isSharedCheck_3127_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_diag_3116_);
lean_inc(v_postponed_3115_);
lean_inc(v_zetaDeltaFVarIds_3114_);
lean_inc(v_mctx_3113_);
lean_dec(v___x_3112_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3127_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 1, v___x_2974_);
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_mctx_3113_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_zetaDeltaFVarIds_3114_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_postponed_3115_);
lean_ctor_set(v_reuseFailAlloc_3126_, 4, v_diag_3116_);
v___x_3121_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_st_ref_put(v___y_2888_, v___x_3121_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3074_);
v___x_3124_ = v___x_3093_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3074_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2974_, 7);
lean_dec(v_brecOnEqName_2885_);
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_a_3080_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_levelParams_2881_);
v_a_3136_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3081_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3081_);
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
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3078_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_levelParams_2881_);
v_a_3144_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3079_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3079_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_dec(v_a_3067_);
lean_dec(v_a_3064_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_levelParams_2881_);
return v___x_3076_;
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3067_);
lean_dec(v_a_3064_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_levelParams_2881_);
v_a_3152_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3072_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3072_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
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
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3064_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3160_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3066_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3066_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3168_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3063_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3063_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v___x_3059_);
lean_dec_ref(v___x_3057_);
lean_del_object(v___x_2997_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3176_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3060_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3060_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
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
lean_dec(v_a_2987_);
lean_dec_ref(v___x_2979_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_2983_);
lean_dec_ref(v___x_2979_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3201_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_2984_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_2984_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___x_2979_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3209_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_2982_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_2982_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v___x_2979_);
lean_dec_ref_known(v___x_2974_, 7);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec_ref(v___x_2875_);
v_a_3217_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_2980_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_2980_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
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
lean_dec(v_a_2930_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
return v___x_2936_;
}
}
}
}
else
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3244_; 
lean_dec(v_a_2925_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
v_a_3237_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3239_ = v___x_2926_;
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_2926_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3244_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3242_; 
if (v_isShared_3240_ == 0)
{
v___x_3242_ = v___x_3239_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
v___x_3242_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
return v___x_3242_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v___x_2908_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
v_a_3245_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_2924_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_2924_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3260_; 
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2916_);
lean_dec_ref(v___x_2914_);
lean_dec_ref(v___x_2908_);
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
v_a_3253_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3255_ = v___x_2920_;
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_2920_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3260_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3258_; 
if (v_isShared_3256_ == 0)
{
v___x_3258_ = v___x_3255_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_del_object(v___x_2902_);
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v___x_2867_);
v_a_3261_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_2905_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_2905_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v_fs_2886_);
lean_dec(v_brecOnEqName_2885_);
lean_dec(v_brecOnName_2884_);
lean_dec(v___x_2883_);
lean_dec(v___x_2882_);
lean_dec(v_levelParams_2881_);
lean_dec(v_brecOnGoName_2880_);
lean_dec_ref(v___x_2875_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2864_);
v_a_3271_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_2898_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_2898_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3279_ = _args[0];
lean_object* v_tail_3280_ = _args[1];
lean_object* v_recName_3281_ = _args[2];
lean_object* v___x_3282_ = _args[3];
lean_object* v___x_3283_ = _args[4];
lean_object* v___x_3284_ = _args[5];
lean_object* v___x_3285_ = _args[6];
lean_object* v___x_3286_ = _args[7];
lean_object* v___x_3287_ = _args[8];
lean_object* v___x_3288_ = _args[9];
lean_object* v___x_3289_ = _args[10];
lean_object* v___x_3290_ = _args[11];
lean_object* v___x_3291_ = _args[12];
lean_object* v___x_3292_ = _args[13];
lean_object* v_val_3293_ = _args[14];
lean_object* v___x_3294_ = _args[15];
lean_object* v_brecOnGoName_3295_ = _args[16];
lean_object* v_levelParams_3296_ = _args[17];
lean_object* v___x_3297_ = _args[18];
lean_object* v___x_3298_ = _args[19];
lean_object* v_brecOnName_3299_ = _args[20];
lean_object* v_brecOnEqName_3300_ = _args[21];
lean_object* v_fs_3301_ = _args[22];
lean_object* v___y_3302_ = _args[23];
lean_object* v___y_3303_ = _args[24];
lean_object* v___y_3304_ = _args[25];
lean_object* v___y_3305_ = _args[26];
lean_object* v___y_3306_ = _args[27];
_start:
{
uint8_t v___x_32934__boxed_3307_; lean_object* v_res_3308_; 
v___x_32934__boxed_3307_ = lean_unbox(v___x_3294_);
v_res_3308_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3279_, v_tail_3280_, v_recName_3281_, v___x_3282_, v___x_3283_, v___x_3284_, v___x_3285_, v___x_3286_, v___x_3287_, v___x_3288_, v___x_3289_, v___x_3290_, v___x_3291_, v___x_3292_, v_val_3293_, v___x_32934__boxed_3307_, v_brecOnGoName_3295_, v_levelParams_3296_, v___x_3297_, v___x_3298_, v_brecOnName_3299_, v_brecOnEqName_3300_, v_fs_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_val_3293_);
lean_dec_ref(v___x_3292_);
lean_dec(v___x_3291_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3286_);
lean_dec(v___x_3285_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3309_, lean_object* v_a_3310_, uint8_t v___x_3311_, lean_object* v_f_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; uint8_t v___x_3321_; lean_object* v___x_3322_; 
lean_inc_ref(v_targs_3309_);
v___x_3318_ = lean_array_push(v_targs_3309_, v_f_3312_);
v___x_3319_ = l_Lean_mkAppN(v_a_3310_, v_targs_3309_);
lean_dec_ref(v_targs_3309_);
v___x_3320_ = 0;
v___x_3321_ = 1;
v___x_3322_ = l_Lean_Meta_mkForallFVars(v___x_3318_, v___x_3319_, v___x_3320_, v___x_3311_, v___x_3311_, v___x_3321_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec_ref(v___x_3318_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3323_, lean_object* v_a_3324_, lean_object* v___x_3325_, lean_object* v_f_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
uint8_t v___x_33655__boxed_3332_; lean_object* v_res_3333_; 
v___x_33655__boxed_3332_ = lean_unbox(v___x_3325_);
v_res_3333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3323_, v_a_3324_, v___x_33655__boxed_3332_, v_f_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3337_, uint8_t v___x_3338_, lean_object* v___x_3339_, lean_object* v_targs_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3347_ = lean_box(v___x_3338_);
lean_inc_ref(v_targs_3340_);
v___f_3348_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3348_, 0, v_targs_3340_);
lean_closure_set(v___f_3348_, 1, v_a_3337_);
lean_closure_set(v___f_3348_, 2, v___x_3347_);
v___x_3349_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3350_ = l_Lean_mkAppN(v___x_3339_, v_targs_3340_);
lean_dec_ref(v_targs_3340_);
v___x_3351_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3349_, v___x_3350_, v___f_3348_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3352_, lean_object* v___x_3353_, lean_object* v___x_3354_, lean_object* v_targs_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_){
_start:
{
uint8_t v___x_33689__boxed_3362_; lean_object* v_res_3363_; 
v___x_33689__boxed_3362_ = lean_unbox(v___x_3353_);
v_res_3363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3352_, v___x_33689__boxed_3362_, v___x_3354_, v_targs_3355_, v_x_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
lean_dec(v___y_3360_);
lean_dec_ref(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec_ref(v_x_3356_);
return v_res_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3364_, lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v_a_3364_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3372_, lean_object* v_x_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3372_, v_x_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v_x_3373_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3381_, lean_object* v___x_3382_, lean_object* v_as_3383_, size_t v_sz_3384_, size_t v_i_3385_, lean_object* v_b_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_usize_dec_lt(v_i_3385_, v_sz_3384_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; 
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v_b_3386_);
return v___x_3393_;
}
else
{
lean_object* v_snd_3394_; lean_object* v_fst_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3492_; 
v_snd_3394_ = lean_ctor_get(v_b_3386_, 1);
v_fst_3395_ = lean_ctor_get(v_b_3386_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_b_3386_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3397_ = v_b_3386_;
v_isShared_3398_ = v_isSharedCheck_3492_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3394_);
lean_inc(v_fst_3395_);
lean_dec(v_b_3386_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3492_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_fst_3399_; lean_object* v_snd_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3491_; 
v_fst_3399_ = lean_ctor_get(v_snd_3394_, 0);
v_snd_3400_ = lean_ctor_get(v_snd_3394_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_snd_3394_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3402_ = v_snd_3394_;
v_isShared_3403_ = v_isSharedCheck_3491_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_snd_3400_);
lean_inc(v_fst_3399_);
lean_dec(v_snd_3394_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3491_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_next_3412_; 
v_next_3412_ = lean_ctor_get(v_snd_3400_, 0);
lean_inc(v_next_3412_);
if (lean_obj_tag(v_next_3412_) == 0)
{
goto v___jp_3404_;
}
else
{
lean_object* v_upperBound_3413_; lean_object* v_val_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3490_; 
v_upperBound_3413_ = lean_ctor_get(v_snd_3400_, 1);
v_val_3414_ = lean_ctor_get(v_next_3412_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v_next_3412_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3416_ = v_next_3412_;
v_isShared_3417_ = v_isSharedCheck_3490_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_val_3414_);
lean_dec(v_next_3412_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3490_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_nat_dec_lt(v_val_3414_, v_upperBound_3413_);
if (v___x_3418_ == 0)
{
lean_del_object(v___x_3416_);
lean_dec(v_val_3414_);
goto v___jp_3404_;
}
else
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3487_; 
lean_inc(v_upperBound_3413_);
lean_del_object(v___x_3402_);
lean_del_object(v___x_3397_);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_snd_3400_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; 
v_unused_3488_ = lean_ctor_get(v_snd_3400_, 1);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_snd_3400_, 0);
lean_dec(v_unused_3489_);
v___x_3420_ = v_snd_3400_;
v_isShared_3421_ = v_isSharedCheck_3487_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v_snd_3400_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3487_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v_array_3422_; lean_object* v_start_3423_; lean_object* v_stop_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3428_; 
v_array_3422_ = lean_ctor_get(v_fst_3399_, 0);
v_start_3423_ = lean_ctor_get(v_fst_3399_, 1);
v_stop_3424_ = lean_ctor_get(v_fst_3399_, 2);
v___x_3425_ = lean_unsigned_to_nat(1u);
v___x_3426_ = lean_nat_add(v_val_3414_, v___x_3425_);
lean_dec(v_val_3414_);
lean_inc(v___x_3426_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3426_);
v___x_3428_ = v___x_3416_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3428_);
v___x_3430_ = v___x_3420_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3428_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_upperBound_3413_);
v___x_3430_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_nat_dec_lt(v_start_3423_, v_stop_3424_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v___x_3426_);
v___x_3432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3432_, 0, v_fst_3399_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
v___x_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3433_, 0, v_fst_3395_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
return v___x_3434_;
}
else
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3481_; 
lean_inc(v_stop_3424_);
lean_inc(v_start_3423_);
lean_inc_ref(v_array_3422_);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_fst_3399_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; lean_object* v_unused_3484_; 
v_unused_3482_ = lean_ctor_get(v_fst_3399_, 2);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_fst_3399_, 1);
lean_dec(v_unused_3483_);
v_unused_3484_ = lean_ctor_get(v_fst_3399_, 0);
lean_dec(v_unused_3484_);
v___x_3436_ = v_fst_3399_;
v_isShared_3437_ = v_isSharedCheck_3481_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v_fst_3399_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3481_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; lean_object* v_a_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3438_ = lean_nat_dec_lt(v___x_3381_, v___x_3382_);
v_a_3439_ = lean_array_uget_borrowed(v_as_3383_, v_i_3385_);
v___x_3440_ = lean_array_fget_borrowed(v_array_3422_, v_start_3423_);
v___x_3441_ = lean_box(v___x_3438_);
lean_inc(v___x_3440_);
lean_inc(v_a_3439_);
v___f_3442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3442_, 0, v_a_3439_);
lean_closure_set(v___f_3442_, 1, v___x_3441_);
lean_closure_set(v___f_3442_, 2, v___x_3440_);
v___x_3443_ = lean_nat_add(v_start_3423_, v___x_3425_);
lean_dec(v_start_3423_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 1, v___x_3443_);
v___x_3445_ = v___x_3436_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_array_3422_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_stop_3424_);
v___x_3445_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
lean_inc(v___y_3390_);
lean_inc_ref(v___y_3389_);
lean_inc(v___y_3388_);
lean_inc_ref(v___y_3387_);
lean_inc(v_a_3439_);
v___x_3446_ = lean_infer_type(v_a_3439_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___x_3448_ = 0;
v___x_3449_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3447_, v___f_3442_, v___x_3448_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___f_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; size_t v___x_3461_; size_t v___x_3462_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___f_3451_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3451_, 0, v_a_3450_);
v___x_3452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3453_ = l_Nat_reprFast(v___x_3426_);
v___x_3454_ = lean_string_append(v___x_3452_, v___x_3453_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = lean_box(0);
v___x_3456_ = l_Lean_Name_str___override(v___x_3455_, v___x_3454_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___f_3451_);
v___x_3458_ = lean_array_push(v_fst_3395_, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3445_);
lean_ctor_set(v___x_3459_, 1, v___x_3430_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3385_, v___x_3461_);
v_i_3385_ = v___x_3462_;
v_b_3386_ = v___x_3460_;
goto _start;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v___x_3445_);
lean_dec_ref(v___x_3430_);
lean_dec(v___x_3426_);
lean_dec(v_fst_3395_);
v_a_3464_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3449_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3449_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec_ref(v___x_3445_);
lean_dec_ref(v___f_3442_);
lean_dec_ref(v___x_3430_);
lean_dec(v___x_3426_);
lean_dec(v_fst_3395_);
v_a_3472_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3446_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3446_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
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
v___jp_3404_:
{
lean_object* v___x_3406_; 
if (v_isShared_3403_ == 0)
{
v___x_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_fst_3399_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_snd_3400_);
v___x_3406_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3408_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 1, v___x_3406_);
v___x_3408_ = v___x_3397_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_fst_3395_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3493_, lean_object* v___x_3494_, lean_object* v_as_3495_, lean_object* v_sz_3496_, lean_object* v_i_3497_, lean_object* v_b_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
size_t v_sz_boxed_3504_; size_t v_i_boxed_3505_; lean_object* v_res_3506_; 
v_sz_boxed_3504_ = lean_unbox_usize(v_sz_3496_);
lean_dec(v_sz_3496_);
v_i_boxed_3505_ = lean_unbox_usize(v_i_3497_);
lean_dec(v_i_3497_);
v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3493_, v___x_3494_, v_as_3495_, v_sz_boxed_3504_, v_i_boxed_3505_, v_b_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v_as_3495_);
lean_dec(v___x_3494_);
lean_dec(v___x_3493_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3507_, size_t v_i_3508_, lean_object* v_bs_3509_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_usize_dec_lt(v_i_3508_, v_sz_3507_);
if (v___x_3510_ == 0)
{
return v_bs_3509_;
}
else
{
lean_object* v_v_3511_; lean_object* v_fst_3512_; lean_object* v_snd_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3529_; 
v_v_3511_ = lean_array_uget(v_bs_3509_, v_i_3508_);
v_fst_3512_ = lean_ctor_get(v_v_3511_, 0);
v_snd_3513_ = lean_ctor_get(v_v_3511_, 1);
v_isSharedCheck_3529_ = !lean_is_exclusive(v_v_3511_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3515_ = v_v_3511_;
v_isShared_3516_ = v_isSharedCheck_3529_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_snd_3513_);
lean_inc(v_fst_3512_);
lean_dec(v_v_3511_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3529_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3517_; lean_object* v_bs_x27_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3522_; 
v___x_3517_ = lean_unsigned_to_nat(0u);
v_bs_x27_3518_ = lean_array_uset(v_bs_3509_, v_i_3508_, v___x_3517_);
v___x_3519_ = 0;
v___x_3520_ = lean_box(v___x_3519_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3520_);
v___x_3522_ = v___x_3515_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3520_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v_snd_3513_);
v___x_3522_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
lean_object* v___x_3523_; size_t v___x_3524_; size_t v___x_3525_; lean_object* v___x_3526_; 
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v_fst_3512_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = ((size_t)1ULL);
v___x_3525_ = lean_usize_add(v_i_3508_, v___x_3524_);
v___x_3526_ = lean_array_uset(v_bs_x27_3518_, v_i_3508_, v___x_3523_);
v_i_3508_ = v___x_3525_;
v_bs_3509_ = v___x_3526_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3530_, lean_object* v_i_3531_, lean_object* v_bs_3532_){
_start:
{
size_t v_sz_boxed_3533_; size_t v_i_boxed_3534_; lean_object* v_res_3535_; 
v_sz_boxed_3533_ = lean_unbox_usize(v_sz_3530_);
lean_dec(v_sz_3530_);
v_i_boxed_3534_ = lean_unbox_usize(v_i_3531_);
lean_dec(v_i_3531_);
v_res_3535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3533_, v_i_boxed_3534_, v_bs_3532_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3536_, lean_object* v___x_3537_, lean_object* v_a_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_32482__overap_3544_; lean_object* v___x_3545_; 
v___x_32482__overap_3544_ = l_instInhabitedOfMonad___redArg(v___x_3536_, v___x_3537_);
lean_inc(v___y_3542_);
lean_inc_ref(v___y_3541_);
lean_inc(v___y_3540_);
lean_inc_ref(v___y_3539_);
v___x_3545_ = lean_apply_5(v___x_32482__overap_3544_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, lean_box(0));
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3546_, lean_object* v___x_3547_, lean_object* v_a_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3546_, v___x_3547_, v_a_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_a_3548_);
return v_res_3554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_instMonadEIO___redArg();
return v___x_3555_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3557_ = l_StateRefT_x27_instMonad___redArg(v___x_3556_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3562_, lean_object* v_declInfos_3563_, lean_object* v_k_3564_, lean_object* v_kind_3565_, lean_object* v_b_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_){
_start:
{
uint8_t v_kind_boxed_3572_; lean_object* v_res_3573_; 
v_kind_boxed_3572_ = lean_unbox(v_kind_3565_);
v_res_3573_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3562_, v_declInfos_3563_, v_k_3564_, v_kind_boxed_3572_, v_b_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3574_, lean_object* v_declInfos_3575_, lean_object* v_k_3576_, uint8_t v_kind_3577_, lean_object* v_name_3578_, uint8_t v_bi_3579_, lean_object* v_type_3580_, uint8_t v_kind_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; lean_object* v___f_3588_; lean_object* v___x_3589_; 
v___x_3587_ = lean_box(v_kind_3577_);
v___f_3588_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3588_, 0, v_acc_3574_);
lean_closure_set(v___f_3588_, 1, v_declInfos_3575_);
lean_closure_set(v___f_3588_, 2, v_k_3576_);
lean_closure_set(v___f_3588_, 3, v___x_3587_);
v___x_3589_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3578_, v_bi_3579_, v_type_3580_, v___f_3588_, v_kind_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
v_a_3598_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3589_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3589_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3606_, lean_object* v_k_3607_, uint8_t v_kind_3608_, lean_object* v_acc_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; lean_object* v_toApplicative_3616_; lean_object* v_toFunctor_3617_; lean_object* v_toSeq_3618_; lean_object* v_toSeqLeft_3619_; lean_object* v_toSeqRight_3620_; lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_toApplicative_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3688_; 
v___x_3615_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3616_ = lean_ctor_get(v___x_3615_, 0);
v_toFunctor_3617_ = lean_ctor_get(v_toApplicative_3616_, 0);
v_toSeq_3618_ = lean_ctor_get(v_toApplicative_3616_, 2);
v_toSeqLeft_3619_ = lean_ctor_get(v_toApplicative_3616_, 3);
v_toSeqRight_3620_ = lean_ctor_get(v_toApplicative_3616_, 4);
v___f_3621_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3622_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3617_, 2);
v___f_3623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3623_, 0, v_toFunctor_3617_);
v___f_3624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3624_, 0, v_toFunctor_3617_);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___f_3623_);
lean_ctor_set(v___x_3625_, 1, v___f_3624_);
lean_inc(v_toSeqRight_3620_);
v___f_3626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3626_, 0, v_toSeqRight_3620_);
lean_inc(v_toSeqLeft_3619_);
v___f_3627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3627_, 0, v_toSeqLeft_3619_);
lean_inc(v_toSeq_3618_);
v___f_3628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3628_, 0, v_toSeq_3618_);
v___x_3629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3625_);
lean_ctor_set(v___x_3629_, 1, v___f_3621_);
lean_ctor_set(v___x_3629_, 2, v___f_3628_);
lean_ctor_set(v___x_3629_, 3, v___f_3627_);
lean_ctor_set(v___x_3629_, 4, v___f_3626_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3629_);
lean_ctor_set(v___x_3630_, 1, v___f_3622_);
v___x_3631_ = l_StateRefT_x27_instMonad___redArg(v___x_3630_);
v_toApplicative_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v___x_3631_, 1);
lean_dec(v_unused_3689_);
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3688_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_toApplicative_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3688_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_toFunctor_3636_; lean_object* v_toSeq_3637_; lean_object* v_toSeqLeft_3638_; lean_object* v_toSeqRight_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3686_; 
v_toFunctor_3636_ = lean_ctor_get(v_toApplicative_3632_, 0);
v_toSeq_3637_ = lean_ctor_get(v_toApplicative_3632_, 2);
v_toSeqLeft_3638_ = lean_ctor_get(v_toApplicative_3632_, 3);
v_toSeqRight_3639_ = lean_ctor_get(v_toApplicative_3632_, 4);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_toApplicative_3632_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v_toApplicative_3632_, 1);
lean_dec(v_unused_3687_);
v___x_3641_ = v_toApplicative_3632_;
v_isShared_3642_ = v_isSharedCheck_3686_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_toSeqRight_3639_);
lean_inc(v_toSeqLeft_3638_);
lean_inc(v_toSeq_3637_);
lean_inc(v_toFunctor_3636_);
lean_dec(v_toApplicative_3632_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3686_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___f_3643_; lean_object* v___f_3644_; lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___x_3647_; lean_object* v___f_3648_; lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___x_3652_; 
v___f_3643_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3644_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3636_);
v___f_3645_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3645_, 0, v_toFunctor_3636_);
v___f_3646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3646_, 0, v_toFunctor_3636_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___f_3645_);
lean_ctor_set(v___x_3647_, 1, v___f_3646_);
v___f_3648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3648_, 0, v_toSeqRight_3639_);
v___f_3649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3649_, 0, v_toSeqLeft_3638_);
v___f_3650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3650_, 0, v_toSeq_3637_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 4, v___f_3648_);
lean_ctor_set(v___x_3641_, 3, v___f_3649_);
lean_ctor_set(v___x_3641_, 2, v___f_3650_);
lean_ctor_set(v___x_3641_, 1, v___f_3643_);
lean_ctor_set(v___x_3641_, 0, v___x_3647_);
v___x_3652_ = v___x_3641_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v___f_3643_);
lean_ctor_set(v_reuseFailAlloc_3685_, 2, v___f_3650_);
lean_ctor_set(v_reuseFailAlloc_3685_, 3, v___f_3649_);
lean_ctor_set(v_reuseFailAlloc_3685_, 4, v___f_3648_);
v___x_3652_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_object* v___x_3654_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 1, v___f_3644_);
lean_ctor_set(v___x_3634_, 0, v___x_3652_);
v___x_3654_ = v___x_3634_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___f_3644_);
v___x_3654_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3655_ = lean_array_get_size(v_acc_3609_);
v___x_3656_ = lean_array_get_size(v_declInfos_3606_);
v___x_3657_ = lean_nat_dec_lt(v___x_3655_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_object* v___x_3658_; 
lean_dec_ref(v___x_3654_);
lean_dec_ref(v_declInfos_3606_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
v___x_3658_ = lean_apply_6(v_k_3607_, v_acc_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, lean_box(0));
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v_snd_3668_; lean_object* v_fst_3669_; lean_object* v_fst_3670_; lean_object* v_snd_3671_; lean_object* v___x_3672_; 
v___x_3659_ = lean_box(0);
v___x_3660_ = 0;
v___x_3661_ = l_Lean_instInhabitedExpr;
v___f_3662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3662_, 0, v___x_3654_);
lean_closure_set(v___f_3662_, 1, v___x_3661_);
v___f_3663_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3663_, 0, v___f_3662_);
v___x_3664_ = lean_box(v___x_3660_);
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
lean_ctor_set(v___x_3665_, 1, v___f_3663_);
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3659_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_array_get(v___x_3666_, v_declInfos_3606_, v___x_3655_);
lean_dec_ref_known(v___x_3666_, 2);
v_snd_3668_ = lean_ctor_get(v___x_3667_, 1);
lean_inc(v_snd_3668_);
v_fst_3669_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_fst_3669_);
lean_dec(v___x_3667_);
v_fst_3670_ = lean_ctor_get(v_snd_3668_, 0);
lean_inc(v_fst_3670_);
v_snd_3671_ = lean_ctor_get(v_snd_3668_, 1);
lean_inc(v_snd_3671_);
lean_dec(v_snd_3668_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc_ref(v_acc_3609_);
v___x_3672_ = lean_apply_6(v_snd_3671_, v_acc_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, lean_box(0));
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
lean_dec_ref_known(v___x_3672_, 1);
v___x_3674_ = lean_unbox(v_fst_3670_);
lean_dec(v_fst_3670_);
v___x_3675_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3609_, v_declInfos_3606_, v_k_3607_, v_kind_3608_, v_fst_3669_, v___x_3674_, v_a_3673_, v_kind_3608_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v___x_3675_;
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v_fst_3670_);
lean_dec(v_fst_3669_);
lean_dec_ref(v_acc_3609_);
lean_dec_ref(v_k_3607_);
lean_dec_ref(v_declInfos_3606_);
v_a_3676_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3672_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3672_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3690_, lean_object* v_declInfos_3691_, lean_object* v_k_3692_, uint8_t v_kind_3693_, lean_object* v_b_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_array_push(v_acc_3690_, v_b_3694_);
v___x_3701_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3691_, v_k_3692_, v_kind_3693_, v___x_3700_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3702_, lean_object* v_declInfos_3703_, lean_object* v_k_3704_, lean_object* v_kind_3705_, lean_object* v_name_3706_, lean_object* v_bi_3707_, lean_object* v_type_3708_, lean_object* v_kind_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_kind_boxed_3715_; uint8_t v_bi_boxed_3716_; uint8_t v_kind_boxed_3717_; lean_object* v_res_3718_; 
v_kind_boxed_3715_ = lean_unbox(v_kind_3705_);
v_bi_boxed_3716_ = lean_unbox(v_bi_3707_);
v_kind_boxed_3717_ = lean_unbox(v_kind_3709_);
v_res_3718_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3702_, v_declInfos_3703_, v_k_3704_, v_kind_boxed_3715_, v_name_3706_, v_bi_boxed_3716_, v_type_3708_, v_kind_boxed_3717_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3719_, lean_object* v_k_3720_, lean_object* v_kind_3721_, lean_object* v_acc_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v_kind_boxed_3728_; lean_object* v_res_3729_; 
v_kind_boxed_3728_ = lean_unbox(v_kind_3721_);
v_res_3729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3719_, v_k_3720_, v_kind_boxed_3728_, v_acc_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3730_, lean_object* v_k_3731_, uint8_t v_kind_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3739_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3730_, v_k_3731_, v_kind_3732_, v___x_3738_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3740_, lean_object* v_k_3741_, lean_object* v_kind_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
uint8_t v_kind_boxed_3748_; lean_object* v_res_3749_; 
v_kind_boxed_3748_ = lean_unbox(v_kind_3742_);
v_res_3749_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3740_, v_k_3741_, v_kind_boxed_3748_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3750_, lean_object* v_k_3751_, uint8_t v_kind_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
size_t v_sz_3758_; size_t v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v_sz_3758_ = lean_array_size(v_declInfos_3750_);
v___x_3759_ = ((size_t)0ULL);
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3758_, v___x_3759_, v_declInfos_3750_);
v___x_3761_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3760_, v_k_3751_, v_kind_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3762_, lean_object* v_k_3763_, lean_object* v_kind_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
uint8_t v_kind_boxed_3770_; lean_object* v_res_3771_; 
v_kind_boxed_3770_ = lean_unbox(v_kind_3764_);
v_res_3771_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3762_, v_k_3763_, v_kind_boxed_3770_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
return v_res_3771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3774_ = lean_unsigned_to_nat(4u);
v___x_3775_ = lean_unsigned_to_nat(202u);
v___x_3776_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3777_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3778_ = l_mkPanicMessageWithDecl(v___x_3777_, v___x_3776_, v___x_3775_, v___x_3774_, v___x_3773_);
return v___x_3778_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3785_ = l_Lean_stringToMessageData(v___x_3784_);
return v___x_3785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3788_ = l_Lean_stringToMessageData(v___x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3789_, lean_object* v_numMotives_3790_, lean_object* v_numMinors_3791_, lean_object* v___x_3792_, lean_object* v_all_3793_, lean_object* v___x_3794_, lean_object* v___x_3795_, lean_object* v_head_3796_, lean_object* v_tail_3797_, lean_object* v_recName_3798_, lean_object* v_brecOnGoName_3799_, lean_object* v_levelParams_3800_, lean_object* v_brecOnName_3801_, lean_object* v_brecOnEqName_3802_, lean_object* v_type_3803_, lean_object* v_refArgs_3804_, lean_object* v_refBody_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
v___x_3811_ = lean_nat_add(v_nParams_3789_, v_numMotives_3790_);
v___x_3812_ = lean_nat_add(v___x_3811_, v_numMinors_3791_);
v___x_3813_ = lean_array_get_size(v_refArgs_3804_);
v___x_3814_ = lean_nat_dec_lt(v___x_3812_, v___x_3813_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v___x_3812_);
lean_dec(v___x_3811_);
lean_dec_ref(v_refArgs_3804_);
lean_dec_ref(v_type_3803_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3794_);
lean_dec_ref(v_all_3793_);
lean_dec(v___x_3792_);
lean_dec(v_nParams_3789_);
v___x_3815_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3816_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3815_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3817_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3789_);
lean_inc_ref_n(v_refArgs_3804_, 2);
v___x_3818_ = l_Array_toSubarray___redArg(v_refArgs_3804_, v___x_3817_, v_nParams_3789_);
lean_inc(v___x_3811_);
v___x_3819_ = l_Array_toSubarray___redArg(v_refArgs_3804_, v_nParams_3789_, v___x_3811_);
v___x_3820_ = l_Subarray_copy___redArg(v___x_3819_);
v___x_3821_ = l_Lean_Expr_getAppFn(v_refBody_3805_);
v___x_3822_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3820_, v___x_3821_);
lean_dec_ref(v___x_3821_);
if (lean_obj_tag(v___x_3822_) == 1)
{
lean_object* v_val_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___f_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec_ref(v_type_3803_);
v_val_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_val_3823_);
lean_dec_ref_known(v___x_3822_, 1);
lean_inc_n(v___x_3812_, 2);
lean_inc_ref_n(v_refArgs_3804_, 2);
v___x_3824_ = l_Array_toSubarray___redArg(v_refArgs_3804_, v___x_3811_, v___x_3812_);
v___x_3825_ = l_Subarray_copy___redArg(v___x_3818_);
v___x_3826_ = l_Subarray_copy___redArg(v___x_3824_);
v___x_3827_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3820_);
lean_inc_ref(v___x_3825_);
lean_inc(v___x_3792_);
v___f_3828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3828_, 0, v___x_3792_);
lean_closure_set(v___f_3828_, 1, v___x_3825_);
lean_closure_set(v___f_3828_, 2, v___x_3820_);
lean_closure_set(v___f_3828_, 3, v_all_3793_);
lean_closure_set(v___f_3828_, 4, v___x_3794_);
lean_closure_set(v___f_3828_, 5, v___x_3817_);
lean_closure_set(v___f_3828_, 6, v___x_3827_);
v___x_3829_ = lean_nat_sub(v___x_3813_, v___x_3827_);
lean_inc(v___x_3829_);
v___x_3830_ = l_Array_toSubarray___redArg(v_refArgs_3804_, v___x_3812_, v___x_3829_);
v___x_3831_ = l_Subarray_copy___redArg(v___x_3830_);
v___x_3832_ = lean_array_get(v___x_3795_, v_refArgs_3804_, v___x_3829_);
lean_dec(v___x_3829_);
lean_dec_ref(v_refArgs_3804_);
lean_inc(v___y_3809_);
lean_inc_ref(v___y_3808_);
lean_inc(v___y_3807_);
lean_inc_ref(v___y_3806_);
lean_inc(v___x_3832_);
v___x_3833_ = lean_infer_type(v___x_3832_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; lean_object* v___x_3835_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
lean_inc(v___y_3809_);
lean_inc_ref(v___y_3808_);
lean_inc(v___y_3807_);
lean_inc_ref(v___y_3806_);
v___x_3835_ = lean_infer_type(v_a_3834_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v_a_3836_; lean_object* v___x_3837_; 
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3837_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3836_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
if (lean_obj_tag(v_a_3838_) == 1)
{
lean_object* v_val_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; size_t v_sz_3852_; size_t v___x_3853_; lean_object* v___x_3854_; 
v_val_3839_ = lean_ctor_get(v_a_3838_, 0);
lean_inc(v_val_3839_);
lean_dec_ref_known(v_a_3838_, 1);
v___x_3840_ = l_Lean_mkLevelMax(v_val_3839_, v_head_3796_);
v___x_3841_ = lean_array_get_size(v___x_3820_);
v___x_3842_ = l_Array_ofFn___redArg(v___x_3841_, v___f_3828_);
v___x_3843_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3844_ = lean_array_get_size(v___x_3842_);
lean_inc_ref(v___x_3842_);
v___x_3845_ = l_Array_toSubarray___redArg(v___x_3842_, v___x_3817_, v___x_3844_);
v___x_3846_ = lean_box(v___x_3814_);
lean_inc(v___x_3812_);
lean_inc_ref(v___x_3820_);
lean_inc_ref(v___x_3845_);
v___f_3847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3847_, 0, v___x_3840_);
lean_closure_set(v___f_3847_, 1, v_tail_3797_);
lean_closure_set(v___f_3847_, 2, v_recName_3798_);
lean_closure_set(v___f_3847_, 3, v___x_3825_);
lean_closure_set(v___f_3847_, 4, v___x_3845_);
lean_closure_set(v___f_3847_, 5, v___x_3820_);
lean_closure_set(v___f_3847_, 6, v___x_3812_);
lean_closure_set(v___f_3847_, 7, v___x_3813_);
lean_closure_set(v___f_3847_, 8, v___x_3826_);
lean_closure_set(v___f_3847_, 9, v___x_3842_);
lean_closure_set(v___f_3847_, 10, v___x_3831_);
lean_closure_set(v___f_3847_, 11, v___x_3832_);
lean_closure_set(v___f_3847_, 12, v___x_3827_);
lean_closure_set(v___f_3847_, 13, v___x_3795_);
lean_closure_set(v___f_3847_, 14, v_val_3823_);
lean_closure_set(v___f_3847_, 15, v___x_3846_);
lean_closure_set(v___f_3847_, 16, v_brecOnGoName_3799_);
lean_closure_set(v___f_3847_, 17, v_levelParams_3800_);
lean_closure_set(v___f_3847_, 18, v___x_3817_);
lean_closure_set(v___f_3847_, 19, v___x_3792_);
lean_closure_set(v___f_3847_, 20, v_brecOnName_3801_);
lean_closure_set(v___f_3847_, 21, v_brecOnEqName_3802_);
v___x_3848_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
lean_ctor_set(v___x_3849_, 1, v___x_3841_);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3845_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3843_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v_sz_3852_ = lean_array_size(v___x_3820_);
v___x_3853_ = ((size_t)0ULL);
v___x_3854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3812_, v___x_3813_, v___x_3820_, v_sz_3852_, v___x_3853_, v___x_3851_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec_ref(v___x_3820_);
lean_dec(v___x_3812_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v_fst_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v_fst_3856_ = lean_ctor_get(v_a_3855_, 0);
lean_inc(v_fst_3856_);
lean_dec(v_a_3855_);
v___x_3857_ = 0;
v___x_3858_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3856_, v___f_3847_, v___x_3857_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3858_;
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v___f_3847_);
v_a_3859_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3854_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3854_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec(v_a_3838_);
lean_dec_ref(v___x_3831_);
lean_dec_ref(v___f_3828_);
lean_dec_ref(v___x_3826_);
lean_dec_ref(v___x_3825_);
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec(v___x_3812_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3792_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3868_ = l_Lean_MessageData_ofExpr(v___x_3832_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___x_3870_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3871_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3872_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v___x_3832_);
lean_dec_ref(v___x_3831_);
lean_dec_ref(v___f_3828_);
lean_dec_ref(v___x_3826_);
lean_dec_ref(v___x_3825_);
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec(v___x_3812_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3792_);
v_a_3873_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3837_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3837_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v___x_3832_);
lean_dec_ref(v___x_3831_);
lean_dec_ref(v___f_3828_);
lean_dec_ref(v___x_3826_);
lean_dec_ref(v___x_3825_);
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec(v___x_3812_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3792_);
v_a_3881_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3835_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3835_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v___x_3832_);
lean_dec_ref(v___x_3831_);
lean_dec_ref(v___f_3828_);
lean_dec_ref(v___x_3826_);
lean_dec_ref(v___x_3825_);
lean_dec(v_val_3823_);
lean_dec_ref(v___x_3820_);
lean_dec(v___x_3812_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3792_);
v_a_3889_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3833_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3833_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v___x_3822_);
lean_dec_ref(v___x_3818_);
lean_dec(v___x_3812_);
lean_dec(v___x_3811_);
lean_dec_ref(v_refArgs_3804_);
lean_dec(v_brecOnEqName_3802_);
lean_dec(v_brecOnName_3801_);
lean_dec(v_levelParams_3800_);
lean_dec(v_brecOnGoName_3799_);
lean_dec(v_recName_3798_);
lean_dec(v_tail_3797_);
lean_dec(v_head_3796_);
lean_dec_ref(v___x_3795_);
lean_dec(v___x_3794_);
lean_dec_ref(v_all_3793_);
lean_dec(v___x_3792_);
v___x_3897_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3898_ = l_Lean_MessageData_ofExpr(v_type_3803_);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = lean_array_to_list(v___x_3820_);
v___x_3903_ = lean_box(0);
v___x_3904_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3902_, v___x_3903_);
v___x_3905_ = l_Lean_MessageData_ofList(v___x_3904_);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3901_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3906_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
return v___x_3907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3908_ = _args[0];
lean_object* v_numMotives_3909_ = _args[1];
lean_object* v_numMinors_3910_ = _args[2];
lean_object* v___x_3911_ = _args[3];
lean_object* v_all_3912_ = _args[4];
lean_object* v___x_3913_ = _args[5];
lean_object* v___x_3914_ = _args[6];
lean_object* v_head_3915_ = _args[7];
lean_object* v_tail_3916_ = _args[8];
lean_object* v_recName_3917_ = _args[9];
lean_object* v_brecOnGoName_3918_ = _args[10];
lean_object* v_levelParams_3919_ = _args[11];
lean_object* v_brecOnName_3920_ = _args[12];
lean_object* v_brecOnEqName_3921_ = _args[13];
lean_object* v_type_3922_ = _args[14];
lean_object* v_refArgs_3923_ = _args[15];
lean_object* v_refBody_3924_ = _args[16];
lean_object* v___y_3925_ = _args[17];
lean_object* v___y_3926_ = _args[18];
lean_object* v___y_3927_ = _args[19];
lean_object* v___y_3928_ = _args[20];
lean_object* v___y_3929_ = _args[21];
_start:
{
lean_object* v_res_3930_; 
v_res_3930_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3908_, v_numMotives_3909_, v_numMinors_3910_, v___x_3911_, v_all_3912_, v___x_3913_, v___x_3914_, v_head_3915_, v_tail_3916_, v_recName_3917_, v_brecOnGoName_3918_, v_levelParams_3919_, v_brecOnName_3920_, v_brecOnEqName_3921_, v_type_3922_, v_refArgs_3923_, v_refBody_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v_refBody_3924_);
lean_dec(v_numMinors_3910_);
lean_dec(v_numMotives_3909_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3933_, lean_object* v_nParams_3934_, lean_object* v_all_3935_, lean_object* v_brecOnName_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v_brecOnGoName_3945_; lean_object* v___x_3946_; lean_object* v_brecOnEqName_3947_; lean_object* v___x_3948_; 
v___x_3942_ = l_Lean_instInhabitedExpr;
v___x_3943_ = lean_box(0);
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3936_, 2);
v_brecOnGoName_3945_ = l_Lean_Name_str___override(v_brecOnName_3936_, v___x_3944_);
v___x_3946_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3947_ = l_Lean_Name_str___override(v_brecOnName_3936_, v___x_3946_);
lean_inc(v_recName_3933_);
v___x_3948_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3933_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3976_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3951_ = v___x_3948_;
v_isShared_3952_ = v_isSharedCheck_3976_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3948_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3976_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
if (lean_obj_tag(v_a_3949_) == 7)
{
lean_object* v_val_3953_; lean_object* v_toConstantVal_3954_; lean_object* v_numMotives_3955_; lean_object* v_numMinors_3956_; lean_object* v_levelParams_3957_; lean_object* v_type_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_del_object(v___x_3951_);
v_val_3953_ = lean_ctor_get(v_a_3949_, 0);
lean_inc_ref(v_val_3953_);
lean_dec_ref_known(v_a_3949_, 1);
v_toConstantVal_3954_ = lean_ctor_get(v_val_3953_, 0);
lean_inc_ref(v_toConstantVal_3954_);
v_numMotives_3955_ = lean_ctor_get(v_val_3953_, 4);
lean_inc(v_numMotives_3955_);
v_numMinors_3956_ = lean_ctor_get(v_val_3953_, 5);
lean_inc(v_numMinors_3956_);
lean_dec_ref(v_val_3953_);
v_levelParams_3957_ = lean_ctor_get(v_toConstantVal_3954_, 1);
lean_inc_n(v_levelParams_3957_, 2);
v_type_3958_ = lean_ctor_get(v_toConstantVal_3954_, 2);
lean_inc_ref(v_type_3958_);
lean_dec_ref(v_toConstantVal_3954_);
v___x_3959_ = lean_box(0);
v___x_3960_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3957_, v___x_3959_);
if (lean_obj_tag(v___x_3960_) == 1)
{
lean_object* v_head_3961_; lean_object* v_tail_3962_; lean_object* v___f_3963_; uint8_t v___x_3964_; lean_object* v___x_3965_; 
v_head_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_head_3961_);
v_tail_3962_ = lean_ctor_get(v___x_3960_, 1);
lean_inc(v_tail_3962_);
lean_inc_ref(v_type_3958_);
v___f_3963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3963_, 0, v_nParams_3934_);
lean_closure_set(v___f_3963_, 1, v_numMotives_3955_);
lean_closure_set(v___f_3963_, 2, v_numMinors_3956_);
lean_closure_set(v___f_3963_, 3, v___x_3960_);
lean_closure_set(v___f_3963_, 4, v_all_3935_);
lean_closure_set(v___f_3963_, 5, v___x_3943_);
lean_closure_set(v___f_3963_, 6, v___x_3942_);
lean_closure_set(v___f_3963_, 7, v_head_3961_);
lean_closure_set(v___f_3963_, 8, v_tail_3962_);
lean_closure_set(v___f_3963_, 9, v_recName_3933_);
lean_closure_set(v___f_3963_, 10, v_brecOnGoName_3945_);
lean_closure_set(v___f_3963_, 11, v_levelParams_3957_);
lean_closure_set(v___f_3963_, 12, v_brecOnName_3936_);
lean_closure_set(v___f_3963_, 13, v_brecOnEqName_3947_);
lean_closure_set(v___f_3963_, 14, v_type_3958_);
v___x_3964_ = 0;
v___x_3965_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3958_, v___f_3963_, v___x_3964_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
return v___x_3965_;
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_dec(v___x_3960_);
lean_dec_ref(v_type_3958_);
lean_dec(v_levelParams_3957_);
lean_dec(v_numMinors_3956_);
lean_dec(v_numMotives_3955_);
lean_dec(v_brecOnEqName_3947_);
lean_dec(v_brecOnGoName_3945_);
lean_dec(v_brecOnName_3936_);
lean_dec_ref(v_all_3935_);
lean_dec(v_nParams_3934_);
v___x_3966_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3967_ = l_Lean_MessageData_ofName(v_recName_3933_);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3966_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3968_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3970_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
return v___x_3971_;
}
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
lean_dec(v_a_3949_);
lean_dec(v_brecOnEqName_3947_);
lean_dec(v_brecOnGoName_3945_);
lean_dec(v_brecOnName_3936_);
lean_dec_ref(v_all_3935_);
lean_dec(v_nParams_3934_);
lean_dec(v_recName_3933_);
v___x_3972_ = lean_box(0);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v___x_3972_);
v___x_3974_ = v___x_3951_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec(v_brecOnEqName_3947_);
lean_dec(v_brecOnGoName_3945_);
lean_dec(v_brecOnName_3936_);
lean_dec_ref(v_all_3935_);
lean_dec(v_nParams_3934_);
lean_dec(v_recName_3933_);
v_a_3977_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3948_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3948_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3985_, lean_object* v_nParams_3986_, lean_object* v_all_3987_, lean_object* v_brecOnName_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3985_, v_nParams_3986_, v_all_3987_, v_brecOnName_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3995_, lean_object* v___x_3996_, lean_object* v___x_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, lean_object* v_a_4000_, lean_object* v_b_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_){
_start:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_lt(v_a_4000_, v_upperBound_3995_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; 
lean_dec(v_a_4000_);
lean_dec_ref(v___x_3999_);
lean_dec(v___x_3998_);
lean_dec(v___x_3997_);
lean_dec(v___x_3996_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v_b_4001_);
return v___x_4008_;
}
else
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4009_ = lean_box(0);
v___x_4010_ = lean_unsigned_to_nat(1u);
v___x_4011_ = lean_nat_add(v_a_4000_, v___x_4010_);
lean_dec(v_a_4000_);
lean_inc_n(v___x_4011_, 2);
lean_inc(v___x_3996_);
v___x_4012_ = lean_name_append_index_after(v___x_3996_, v___x_4011_);
lean_inc(v___x_3997_);
v___x_4013_ = lean_name_append_index_after(v___x_3997_, v___x_4011_);
lean_inc_ref(v___x_3999_);
lean_inc(v___x_3998_);
v___x_4014_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4012_, v___x_3998_, v___x_3999_, v___x_4013_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_dec_ref_known(v___x_4014_, 1);
v_a_4000_ = v___x_4011_;
v_b_4001_ = v___x_4009_;
goto _start;
}
else
{
lean_dec(v___x_4011_);
lean_dec_ref(v___x_3999_);
lean_dec(v___x_3998_);
lean_dec(v___x_3997_);
lean_dec(v___x_3996_);
return v___x_4014_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_4016_, lean_object* v___x_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, lean_object* v___x_4020_, lean_object* v_a_4021_, lean_object* v_b_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4016_, v___x_4017_, v___x_4018_, v___x_4019_, v___x_4020_, v_a_4021_, v_b_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v_upperBound_4016_);
return v_res_4028_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4034_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_4035_ = l_Lean_Name_append(v___x_4034_, v___x_4033_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_toCold_4042_; lean_object* v_options_4043_; lean_object* v_inheritedTraceOptions_4044_; uint8_t v_hasTrace_4045_; lean_object* v___x_4046_; 
v_toCold_4042_ = lean_ctor_get(v_a_4039_, 0);
v_options_4043_ = lean_ctor_get(v_toCold_4042_, 2);
v_inheritedTraceOptions_4044_ = lean_ctor_get(v_toCold_4042_, 11);
v_hasTrace_4045_ = lean_ctor_get_uint8(v_options_4043_, sizeof(void*)*1);
v___x_4046_ = lean_box(0);
if (v_hasTrace_4045_ == 0)
{
lean_object* v___x_4047_; 
lean_inc(v_indName_4036_);
v___x_4047_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4112_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4112_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4112_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
if (lean_obj_tag(v_a_4048_) == 5)
{
lean_object* v_val_4052_; uint8_t v_isRec_4053_; 
v_val_4052_ = lean_ctor_get(v_a_4048_, 0);
lean_inc_ref(v_val_4052_);
lean_dec_ref_known(v_a_4048_, 1);
v_isRec_4053_ = lean_ctor_get_uint8(v_val_4052_, sizeof(void*)*6);
if (v_isRec_4053_ == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4056_; 
lean_dec_ref(v_val_4052_);
lean_dec(v_indName_4036_);
v___x_4054_ = lean_box(0);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4054_);
v___x_4056_ = v___x_4050_;
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
else
{
lean_object* v_toConstantVal_4058_; lean_object* v_numParams_4059_; lean_object* v_all_4060_; lean_object* v_numNested_4061_; lean_object* v_type_4062_; lean_object* v___x_4063_; 
lean_del_object(v___x_4050_);
v_toConstantVal_4058_ = lean_ctor_get(v_val_4052_, 0);
lean_inc_ref(v_toConstantVal_4058_);
v_numParams_4059_ = lean_ctor_get(v_val_4052_, 1);
lean_inc(v_numParams_4059_);
v_all_4060_ = lean_ctor_get(v_val_4052_, 3);
lean_inc(v_all_4060_);
v_numNested_4061_ = lean_ctor_get(v_val_4052_, 5);
lean_inc(v_numNested_4061_);
lean_dec_ref(v_val_4052_);
v_type_4062_ = lean_ctor_get(v_toConstantVal_4058_, 2);
lean_inc_ref(v_type_4062_);
lean_dec_ref(v_toConstantVal_4058_);
v___x_4063_ = l_Lean_Meta_isPropFormerType(v_type_4062_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4099_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4099_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4099_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
uint8_t v___x_4068_; 
v___x_4068_ = lean_unbox(v_a_4064_);
lean_dec(v_a_4064_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_del_object(v___x_4066_);
lean_inc_n(v_indName_4036_, 2);
v___x_4069_ = l_Lean_mkRecName(v_indName_4036_);
v___x_4070_ = l_Lean_mkBRecOnName(v_indName_4036_);
lean_inc(v_all_4060_);
v___x_4071_ = lean_array_mk(v_all_4060_);
lean_inc(v___x_4070_);
lean_inc_ref(v___x_4071_);
lean_inc(v_numParams_4059_);
lean_inc(v___x_4069_);
v___x_4072_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4069_, v_numParams_4059_, v___x_4071_, v___x_4070_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4074_; uint8_t v_isShared_4075_; uint8_t v_isSharedCheck_4093_; 
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4093_ == 0)
{
lean_object* v_unused_4094_; 
v_unused_4094_ = lean_ctor_get(v___x_4072_, 0);
lean_dec(v_unused_4094_);
v___x_4074_ = v___x_4072_;
v_isShared_4075_ = v_isSharedCheck_4093_;
goto v_resetjp_4073_;
}
else
{
lean_dec(v___x_4072_);
v___x_4074_ = lean_box(0);
v_isShared_4075_ = v_isSharedCheck_4093_;
goto v_resetjp_4073_;
}
v_resetjp_4073_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
v___x_4076_ = lean_unsigned_to_nat(0u);
v___x_4077_ = l_List_get_x21Internal___redArg(v___x_4046_, v_all_4060_, v___x_4076_);
lean_dec(v_all_4060_);
v___x_4078_ = lean_name_eq(v___x_4077_, v_indName_4036_);
lean_dec(v_indName_4036_);
lean_dec(v___x_4077_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; lean_object* v___x_4081_; 
lean_dec_ref(v___x_4071_);
lean_dec(v___x_4070_);
lean_dec(v___x_4069_);
lean_dec(v_numNested_4061_);
lean_dec(v_numParams_4059_);
v___x_4079_ = lean_box(0);
if (v_isShared_4075_ == 0)
{
lean_ctor_set(v___x_4074_, 0, v___x_4079_);
v___x_4081_ = v___x_4074_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___x_4079_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_del_object(v___x_4074_);
v___x_4083_ = lean_box(0);
v___x_4084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4061_, v___x_4069_, v___x_4070_, v_numParams_4059_, v___x_4071_, v___x_4076_, v___x_4083_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_numNested_4061_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4091_ == 0)
{
lean_object* v_unused_4092_; 
v_unused_4092_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4092_);
v___x_4086_ = v___x_4084_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v___x_4084_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v___x_4083_);
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v___x_4083_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
else
{
return v___x_4084_;
}
}
}
}
else
{
lean_dec_ref(v___x_4071_);
lean_dec(v___x_4070_);
lean_dec(v___x_4069_);
lean_dec(v_numNested_4061_);
lean_dec(v_all_4060_);
lean_dec(v_numParams_4059_);
lean_dec(v_indName_4036_);
return v___x_4072_;
}
}
else
{
lean_object* v___x_4095_; lean_object* v___x_4097_; 
lean_dec(v_numNested_4061_);
lean_dec(v_all_4060_);
lean_dec(v_numParams_4059_);
lean_dec(v_indName_4036_);
v___x_4095_ = lean_box(0);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4095_);
v___x_4097_ = v___x_4066_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v___x_4095_);
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
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_numNested_4061_);
lean_dec(v_all_4060_);
lean_dec(v_numParams_4059_);
lean_dec(v_indName_4036_);
v_a_4100_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4063_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4063_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
else
{
lean_object* v___x_4108_; lean_object* v___x_4110_; 
lean_dec(v_a_4048_);
lean_dec(v_indName_4036_);
v___x_4108_ = lean_box(0);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4108_);
v___x_4110_ = v___x_4050_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_indName_4036_);
v_a_4113_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4047_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4047_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
else
{
lean_object* v___f_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v_a_4129_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v_a_4144_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v_a_4149_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v_a_4154_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v_a_4166_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v_a_4171_; 
lean_inc(v_indName_4036_);
v___f_4121_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4121_, 0, v_indName_4036_);
v___x_4122_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4123_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4124_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4125_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4044_, v_options_4043_, v___x_4124_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4238_ = l_Lean_trace_profiler;
v___x_4239_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4043_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4240_; 
lean_dec_ref(v___f_4121_);
lean_inc(v_indName_4036_);
v___x_4240_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4305_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4243_ = v___x_4240_;
v_isShared_4244_ = v_isSharedCheck_4305_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4240_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4305_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
if (lean_obj_tag(v_a_4241_) == 5)
{
lean_object* v_val_4245_; uint8_t v_isRec_4246_; 
v_val_4245_ = lean_ctor_get(v_a_4241_, 0);
lean_inc_ref(v_val_4245_);
lean_dec_ref_known(v_a_4241_, 1);
v_isRec_4246_ = lean_ctor_get_uint8(v_val_4245_, sizeof(void*)*6);
if (v_isRec_4246_ == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
lean_dec_ref(v_val_4245_);
lean_dec(v_indName_4036_);
v___x_4247_ = lean_box(0);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4247_);
v___x_4249_ = v___x_4243_;
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
else
{
lean_object* v_toConstantVal_4251_; lean_object* v_numParams_4252_; lean_object* v_all_4253_; lean_object* v_numNested_4254_; lean_object* v_type_4255_; lean_object* v___x_4256_; 
lean_del_object(v___x_4243_);
v_toConstantVal_4251_ = lean_ctor_get(v_val_4245_, 0);
lean_inc_ref(v_toConstantVal_4251_);
v_numParams_4252_ = lean_ctor_get(v_val_4245_, 1);
lean_inc(v_numParams_4252_);
v_all_4253_ = lean_ctor_get(v_val_4245_, 3);
lean_inc(v_all_4253_);
v_numNested_4254_ = lean_ctor_get(v_val_4245_, 5);
lean_inc(v_numNested_4254_);
lean_dec_ref(v_val_4245_);
v_type_4255_ = lean_ctor_get(v_toConstantVal_4251_, 2);
lean_inc_ref(v_type_4255_);
lean_dec_ref(v_toConstantVal_4251_);
v___x_4256_ = l_Lean_Meta_isPropFormerType(v_type_4255_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4292_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4259_ = v___x_4256_;
v_isShared_4260_ = v_isSharedCheck_4292_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4256_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4292_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
uint8_t v___x_4261_; 
v___x_4261_ = lean_unbox(v_a_4257_);
lean_dec(v_a_4257_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_del_object(v___x_4259_);
lean_inc_n(v_indName_4036_, 2);
v___x_4262_ = l_Lean_mkRecName(v_indName_4036_);
v___x_4263_ = l_Lean_mkBRecOnName(v_indName_4036_);
lean_inc(v_all_4253_);
v___x_4264_ = lean_array_mk(v_all_4253_);
lean_inc(v___x_4263_);
lean_inc_ref(v___x_4264_);
lean_inc(v_numParams_4252_);
lean_inc(v___x_4262_);
v___x_4265_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4262_, v_numParams_4252_, v___x_4264_, v___x_4263_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4286_; 
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4286_ == 0)
{
lean_object* v_unused_4287_; 
v_unused_4287_ = lean_ctor_get(v___x_4265_, 0);
lean_dec(v_unused_4287_);
v___x_4267_ = v___x_4265_;
v_isShared_4268_ = v_isSharedCheck_4286_;
goto v_resetjp_4266_;
}
else
{
lean_dec(v___x_4265_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4286_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v___x_4269_ = lean_unsigned_to_nat(0u);
v___x_4270_ = l_List_get_x21Internal___redArg(v___x_4046_, v_all_4253_, v___x_4269_);
lean_dec(v_all_4253_);
v___x_4271_ = lean_name_eq(v___x_4270_, v_indName_4036_);
lean_dec(v_indName_4036_);
lean_dec(v___x_4270_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4274_; 
lean_dec_ref(v___x_4264_);
lean_dec(v___x_4263_);
lean_dec(v___x_4262_);
lean_dec(v_numNested_4254_);
lean_dec(v_numParams_4252_);
v___x_4272_ = lean_box(0);
if (v_isShared_4268_ == 0)
{
lean_ctor_set(v___x_4267_, 0, v___x_4272_);
v___x_4274_ = v___x_4267_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v___x_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
lean_del_object(v___x_4267_);
v___x_4276_ = lean_box(0);
v___x_4277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4254_, v___x_4262_, v___x_4263_, v_numParams_4252_, v___x_4264_, v___x_4269_, v___x_4276_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_numNested_4254_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4284_ == 0)
{
lean_object* v_unused_4285_; 
v_unused_4285_ = lean_ctor_get(v___x_4277_, 0);
lean_dec(v_unused_4285_);
v___x_4279_ = v___x_4277_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_dec(v___x_4277_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
lean_ctor_set(v___x_4279_, 0, v___x_4276_);
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4276_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
else
{
return v___x_4277_;
}
}
}
}
else
{
lean_dec_ref(v___x_4264_);
lean_dec(v___x_4263_);
lean_dec(v___x_4262_);
lean_dec(v_numNested_4254_);
lean_dec(v_all_4253_);
lean_dec(v_numParams_4252_);
lean_dec(v_indName_4036_);
return v___x_4265_;
}
}
else
{
lean_object* v___x_4288_; lean_object* v___x_4290_; 
lean_dec(v_numNested_4254_);
lean_dec(v_all_4253_);
lean_dec(v_numParams_4252_);
lean_dec(v_indName_4036_);
v___x_4288_ = lean_box(0);
if (v_isShared_4260_ == 0)
{
lean_ctor_set(v___x_4259_, 0, v___x_4288_);
v___x_4290_ = v___x_4259_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_numNested_4254_);
lean_dec(v_all_4253_);
lean_dec(v_numParams_4252_);
lean_dec(v_indName_4036_);
v_a_4293_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4256_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4256_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
}
else
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
lean_dec(v_a_4241_);
lean_dec(v_indName_4036_);
v___x_4301_ = lean_box(0);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4301_);
v___x_4303_ = v___x_4243_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4301_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v_indName_4036_);
v_a_4306_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4240_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4240_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
else
{
goto v___jp_4173_;
}
}
else
{
goto v___jp_4173_;
}
v___jp_4126_:
{
lean_object* v___x_4130_; double v___x_4131_; double v___x_4132_; double v___x_4133_; double v___x_4134_; double v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4130_ = lean_io_mono_nanos_now();
v___x_4131_ = lean_float_of_nat(v___y_4127_);
v___x_4132_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4133_ = lean_float_div(v___x_4131_, v___x_4132_);
v___x_4134_ = lean_float_of_nat(v___x_4130_);
v___x_4135_ = lean_float_div(v___x_4134_, v___x_4132_);
v___x_4136_ = lean_box_float(v___x_4133_);
v___x_4137_ = lean_box_float(v___x_4135_);
v___x_4138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4139_, 0, v_a_4129_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4122_, v_hasTrace_4045_, v___x_4123_, v_options_4043_, v___x_4125_, v___y_4128_, v___f_4121_, v___x_4139_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
return v___x_4140_;
}
v___jp_4141_:
{
lean_object* v___x_4145_; 
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v_a_4144_);
v___y_4127_ = v___y_4142_;
v___y_4128_ = v___y_4143_;
v_a_4129_ = v___x_4145_;
goto v___jp_4126_;
}
v___jp_4146_:
{
lean_object* v___x_4150_; 
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_a_4149_);
v___y_4127_ = v___y_4147_;
v___y_4128_ = v___y_4148_;
v_a_4129_ = v___x_4150_;
goto v___jp_4126_;
}
v___jp_4151_:
{
lean_object* v___x_4155_; double v___x_4156_; double v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4155_ = lean_io_get_num_heartbeats();
v___x_4156_ = lean_float_of_nat(v___y_4153_);
v___x_4157_ = lean_float_of_nat(v___x_4155_);
v___x_4158_ = lean_box_float(v___x_4156_);
v___x_4159_ = lean_box_float(v___x_4157_);
v___x_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v_a_4154_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4122_, v_hasTrace_4045_, v___x_4123_, v_options_4043_, v___x_4125_, v___y_4152_, v___f_4121_, v___x_4161_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
return v___x_4162_;
}
v___jp_4163_:
{
lean_object* v___x_4167_; 
v___x_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4167_, 0, v_a_4166_);
v___y_4152_ = v___y_4164_;
v___y_4153_ = v___y_4165_;
v_a_4154_ = v___x_4167_;
goto v___jp_4151_;
}
v___jp_4168_:
{
lean_object* v___x_4172_; 
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v_a_4171_);
v___y_4152_ = v___y_4169_;
v___y_4153_ = v___y_4170_;
v_a_4154_ = v___x_4172_;
goto v___jp_4151_;
}
v___jp_4173_:
{
lean_object* v___x_4174_; lean_object* v_a_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v___x_4174_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_4040_);
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4174_);
v___x_4176_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4177_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4043_, v___x_4176_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_io_mono_nanos_now();
lean_inc(v_indName_4036_);
v___x_4179_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4179_) == 0)
{
lean_object* v_a_4180_; 
v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4180_);
lean_dec_ref_known(v___x_4179_, 1);
if (lean_obj_tag(v_a_4180_) == 5)
{
lean_object* v_val_4181_; uint8_t v_isRec_4182_; 
v_val_4181_ = lean_ctor_get(v_a_4180_, 0);
lean_inc_ref(v_val_4181_);
lean_dec_ref_known(v_a_4180_, 1);
v_isRec_4182_ = lean_ctor_get_uint8(v_val_4181_, sizeof(void*)*6);
if (v_isRec_4182_ == 0)
{
lean_object* v___x_4183_; 
lean_dec_ref(v_val_4181_);
lean_dec(v_indName_4036_);
v___x_4183_ = lean_box(0);
v___y_4142_ = v___x_4178_;
v___y_4143_ = v_a_4175_;
v_a_4144_ = v___x_4183_;
goto v___jp_4141_;
}
else
{
lean_object* v_toConstantVal_4184_; lean_object* v_numParams_4185_; lean_object* v_all_4186_; lean_object* v_numNested_4187_; lean_object* v_type_4188_; lean_object* v___x_4189_; 
v_toConstantVal_4184_ = lean_ctor_get(v_val_4181_, 0);
lean_inc_ref(v_toConstantVal_4184_);
v_numParams_4185_ = lean_ctor_get(v_val_4181_, 1);
lean_inc(v_numParams_4185_);
v_all_4186_ = lean_ctor_get(v_val_4181_, 3);
lean_inc(v_all_4186_);
v_numNested_4187_ = lean_ctor_get(v_val_4181_, 5);
lean_inc(v_numNested_4187_);
lean_dec_ref(v_val_4181_);
v_type_4188_ = lean_ctor_get(v_toConstantVal_4184_, 2);
lean_inc_ref(v_type_4188_);
lean_dec_ref(v_toConstantVal_4184_);
v___x_4189_ = l_Lean_Meta_isPropFormerType(v_type_4188_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; uint8_t v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref_known(v___x_4189_, 1);
v___x_4191_ = lean_unbox(v_a_4190_);
lean_dec(v_a_4190_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
lean_inc_n(v_indName_4036_, 2);
v___x_4192_ = l_Lean_mkRecName(v_indName_4036_);
v___x_4193_ = l_Lean_mkBRecOnName(v_indName_4036_);
lean_inc(v_all_4186_);
v___x_4194_ = lean_array_mk(v_all_4186_);
lean_inc(v___x_4193_);
lean_inc_ref(v___x_4194_);
lean_inc(v_numParams_4185_);
lean_inc(v___x_4192_);
v___x_4195_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4192_, v_numParams_4185_, v___x_4194_, v___x_4193_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; 
lean_dec_ref_known(v___x_4195_, 1);
v___x_4196_ = lean_unsigned_to_nat(0u);
v___x_4197_ = l_List_get_x21Internal___redArg(v___x_4046_, v_all_4186_, v___x_4196_);
lean_dec(v_all_4186_);
v___x_4198_ = lean_name_eq(v___x_4197_, v_indName_4036_);
lean_dec(v_indName_4036_);
lean_dec(v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; 
lean_dec_ref(v___x_4194_);
lean_dec(v___x_4193_);
lean_dec(v___x_4192_);
lean_dec(v_numNested_4187_);
lean_dec(v_numParams_4185_);
v___x_4199_ = lean_box(0);
v___y_4142_ = v___x_4178_;
v___y_4143_ = v_a_4175_;
v_a_4144_ = v___x_4199_;
goto v___jp_4141_;
}
else
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_box(0);
v___x_4201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4187_, v___x_4192_, v___x_4193_, v_numParams_4185_, v___x_4194_, v___x_4196_, v___x_4200_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_numNested_4187_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_dec_ref_known(v___x_4201_, 1);
v___y_4142_ = v___x_4178_;
v___y_4143_ = v_a_4175_;
v_a_4144_ = v___x_4200_;
goto v___jp_4141_;
}
else
{
lean_object* v_a_4202_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v___y_4147_ = v___x_4178_;
v___y_4148_ = v_a_4175_;
v_a_4149_ = v_a_4202_;
goto v___jp_4146_;
}
}
}
else
{
lean_object* v_a_4203_; 
lean_dec_ref(v___x_4194_);
lean_dec(v___x_4193_);
lean_dec(v___x_4192_);
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_indName_4036_);
v_a_4203_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4195_, 1);
v___y_4147_ = v___x_4178_;
v___y_4148_ = v_a_4175_;
v_a_4149_ = v_a_4203_;
goto v___jp_4146_;
}
}
else
{
lean_object* v___x_4204_; 
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_indName_4036_);
v___x_4204_ = lean_box(0);
v___y_4142_ = v___x_4178_;
v___y_4143_ = v_a_4175_;
v_a_4144_ = v___x_4204_;
goto v___jp_4141_;
}
}
else
{
lean_object* v_a_4205_; 
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_indName_4036_);
v_a_4205_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4189_, 1);
v___y_4147_ = v___x_4178_;
v___y_4148_ = v_a_4175_;
v_a_4149_ = v_a_4205_;
goto v___jp_4146_;
}
}
}
else
{
lean_object* v___x_4206_; 
lean_dec(v_a_4180_);
lean_dec(v_indName_4036_);
v___x_4206_ = lean_box(0);
v___y_4142_ = v___x_4178_;
v___y_4143_ = v_a_4175_;
v_a_4144_ = v___x_4206_;
goto v___jp_4141_;
}
}
else
{
lean_object* v_a_4207_; 
lean_dec(v_indName_4036_);
v_a_4207_ = lean_ctor_get(v___x_4179_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4179_, 1);
v___y_4147_ = v___x_4178_;
v___y_4148_ = v_a_4175_;
v_a_4149_ = v_a_4207_;
goto v___jp_4146_;
}
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_4036_);
v___x_4209_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
if (lean_obj_tag(v_a_4210_) == 5)
{
lean_object* v_val_4211_; uint8_t v_isRec_4212_; 
v_val_4211_ = lean_ctor_get(v_a_4210_, 0);
lean_inc_ref(v_val_4211_);
lean_dec_ref_known(v_a_4210_, 1);
v_isRec_4212_ = lean_ctor_get_uint8(v_val_4211_, sizeof(void*)*6);
if (v_isRec_4212_ == 0)
{
lean_object* v___x_4213_; 
lean_dec_ref(v_val_4211_);
lean_dec(v_indName_4036_);
v___x_4213_ = lean_box(0);
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4208_;
v_a_4166_ = v___x_4213_;
goto v___jp_4163_;
}
else
{
lean_object* v_toConstantVal_4214_; lean_object* v_numParams_4215_; lean_object* v_all_4216_; lean_object* v_numNested_4217_; lean_object* v_type_4218_; lean_object* v___x_4219_; 
v_toConstantVal_4214_ = lean_ctor_get(v_val_4211_, 0);
lean_inc_ref(v_toConstantVal_4214_);
v_numParams_4215_ = lean_ctor_get(v_val_4211_, 1);
lean_inc(v_numParams_4215_);
v_all_4216_ = lean_ctor_get(v_val_4211_, 3);
lean_inc(v_all_4216_);
v_numNested_4217_ = lean_ctor_get(v_val_4211_, 5);
lean_inc(v_numNested_4217_);
lean_dec_ref(v_val_4211_);
v_type_4218_ = lean_ctor_get(v_toConstantVal_4214_, 2);
lean_inc_ref(v_type_4218_);
lean_dec_ref(v_toConstantVal_4214_);
v___x_4219_ = l_Lean_Meta_isPropFormerType(v_type_4218_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; uint8_t v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = lean_unbox(v_a_4220_);
lean_dec(v_a_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_inc_n(v_indName_4036_, 2);
v___x_4222_ = l_Lean_mkRecName(v_indName_4036_);
v___x_4223_ = l_Lean_mkBRecOnName(v_indName_4036_);
lean_inc(v_all_4216_);
v___x_4224_ = lean_array_mk(v_all_4216_);
lean_inc(v___x_4223_);
lean_inc_ref(v___x_4224_);
lean_inc(v_numParams_4215_);
lean_inc(v___x_4222_);
v___x_4225_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4222_, v_numParams_4215_, v___x_4224_, v___x_4223_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
lean_dec_ref_known(v___x_4225_, 1);
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_List_get_x21Internal___redArg(v___x_4046_, v_all_4216_, v___x_4226_);
lean_dec(v_all_4216_);
v___x_4228_ = lean_name_eq(v___x_4227_, v_indName_4036_);
lean_dec(v_indName_4036_);
lean_dec(v___x_4227_);
if (v___x_4228_ == 0)
{
lean_object* v___x_4229_; 
lean_dec_ref(v___x_4224_);
lean_dec(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v_numNested_4217_);
lean_dec(v_numParams_4215_);
v___x_4229_ = lean_box(0);
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4208_;
v_a_4166_ = v___x_4229_;
goto v___jp_4163_;
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_box(0);
v___x_4231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4217_, v___x_4222_, v___x_4223_, v_numParams_4215_, v___x_4224_, v___x_4226_, v___x_4230_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
lean_dec(v_numNested_4217_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_dec_ref_known(v___x_4231_, 1);
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4208_;
v_a_4166_ = v___x_4230_;
goto v___jp_4163_;
}
else
{
lean_object* v_a_4232_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___y_4169_ = v_a_4175_;
v___y_4170_ = v___x_4208_;
v_a_4171_ = v_a_4232_;
goto v___jp_4168_;
}
}
}
else
{
lean_object* v_a_4233_; 
lean_dec_ref(v___x_4224_);
lean_dec(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v_numNested_4217_);
lean_dec(v_all_4216_);
lean_dec(v_numParams_4215_);
lean_dec(v_indName_4036_);
v_a_4233_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4225_, 1);
v___y_4169_ = v_a_4175_;
v___y_4170_ = v___x_4208_;
v_a_4171_ = v_a_4233_;
goto v___jp_4168_;
}
}
else
{
lean_object* v___x_4234_; 
lean_dec(v_numNested_4217_);
lean_dec(v_all_4216_);
lean_dec(v_numParams_4215_);
lean_dec(v_indName_4036_);
v___x_4234_ = lean_box(0);
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4208_;
v_a_4166_ = v___x_4234_;
goto v___jp_4163_;
}
}
else
{
lean_object* v_a_4235_; 
lean_dec(v_numNested_4217_);
lean_dec(v_all_4216_);
lean_dec(v_numParams_4215_);
lean_dec(v_indName_4036_);
v_a_4235_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4219_, 1);
v___y_4169_ = v_a_4175_;
v___y_4170_ = v___x_4208_;
v_a_4171_ = v_a_4235_;
goto v___jp_4168_;
}
}
}
else
{
lean_object* v___x_4236_; 
lean_dec(v_a_4210_);
lean_dec(v_indName_4036_);
v___x_4236_ = lean_box(0);
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4208_;
v_a_4166_ = v___x_4236_;
goto v___jp_4163_;
}
}
else
{
lean_object* v_a_4237_; 
lean_dec(v_indName_4036_);
v_a_4237_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4209_, 1);
v___y_4169_ = v_a_4175_;
v___y_4170_ = v___x_4208_;
v_a_4171_ = v_a_4237_;
goto v___jp_4168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_mkBRecOn(v_indName_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4321_, lean_object* v___x_4322_, lean_object* v___x_4323_, lean_object* v___x_4324_, lean_object* v___x_4325_, lean_object* v_inst_4326_, lean_object* v_R_4327_, lean_object* v_a_4328_, lean_object* v_b_4329_, lean_object* v_c_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; 
v___x_4336_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4321_, v___x_4322_, v___x_4323_, v___x_4324_, v___x_4325_, v_a_4328_, v_b_4329_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4337_, lean_object* v___x_4338_, lean_object* v___x_4339_, lean_object* v___x_4340_, lean_object* v___x_4341_, lean_object* v_inst_4342_, lean_object* v_R_4343_, lean_object* v_a_4344_, lean_object* v_b_4345_, lean_object* v_c_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4337_, v___x_4338_, v___x_4339_, v___x_4340_, v___x_4341_, v_inst_4342_, v_R_4343_, v_a_4344_, v_b_4345_, v_c_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v_upperBound_4337_);
return v_res_4352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_unsigned_to_nat(2304625798u);
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4400_ = l_Lean_Name_num___override(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4402_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4403_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4404_ = l_Lean_Name_str___override(v___x_4403_, v___x_4402_);
return v___x_4404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4406_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4407_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4408_ = l_Lean_Name_str___override(v___x_4407_, v___x_4406_);
return v___x_4408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4409_ = lean_unsigned_to_nat(2u);
v___x_4410_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4411_ = l_Lean_Name_num___override(v___x_4410_, v___x_4409_);
return v___x_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4413_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4414_ = 0;
v___x_4415_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4416_ = l_Lean_registerTraceClass(v___x_4413_, v___x_4414_, v___x_4415_);
return v___x_4416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4418_;
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
