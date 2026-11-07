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
lean_object* v___f_435_; lean_object* v___x_5294__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_5294__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_5294__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
uint8_t v___x_9577__boxed_554_; lean_object* v_res_555_; 
v___x_9577__boxed_554_ = lean_unbox(v___x_546_);
v_res_555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_545_, v___x_9577__boxed_554_, v_targs_547_, v_x_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
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
v___x_845_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
lean_ctor_set(v___x_845_, 2, v___x_842_);
lean_ctor_set(v___x_845_, 3, v___x_843_);
lean_ctor_set(v___x_845_, 4, v___x_843_);
lean_ctor_set(v___x_845_, 5, v___x_843_);
lean_ctor_set(v___x_845_, 6, v___x_843_);
lean_ctor_set(v___x_845_, 7, v___x_841_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(lean_object* v_msg_977_, lean_object* v_declHint_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_env_983_; uint8_t v___x_984_; 
v___x_981_ = lean_box(0);
v___x_982_ = lean_st_ref_get(v___y_979_);
v_env_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_ref(v_env_983_);
lean_dec(v___x_982_);
v___x_984_ = l_Lean_Name_isAnonymous(v_declHint_978_);
if (v___x_984_ == 0)
{
uint8_t v_isExporting_985_; 
v_isExporting_985_ = lean_ctor_get_uint8(v_env_983_, sizeof(void*)*13);
if (v_isExporting_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_978_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_msg_977_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
lean_inc_ref(v_env_983_);
v___x_987_ = l_Lean_Environment_setExporting(v_env_983_, v___x_984_);
lean_inc(v_declHint_978_);
lean_inc_ref(v___x_987_);
v___x_988_ = l_Lean_Environment_contains(v___x_987_, v_declHint_978_, v_isExporting_985_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v___x_987_);
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_978_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_msg_977_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_c_995_; lean_object* v___x_996_; 
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__1);
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__4);
v___x_992_ = l_Lean_Options_empty;
lean_inc_ref(v___x_987_);
v___x_993_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_993_, 0, v___x_987_);
lean_ctor_set(v___x_993_, 1, v___x_990_);
lean_ctor_set(v___x_993_, 2, v___x_991_);
lean_ctor_set(v___x_993_, 3, v___x_992_);
lean_inc(v_declHint_978_);
v___x_994_ = l_Lean_MessageData_ofConstName(v_declHint_978_, v___x_984_);
v_c_995_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_995_, 0, v___x_993_);
lean_ctor_set(v_c_995_, 1, v___x_994_);
v___x_996_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_987_, v_declHint_978_);
lean_dec_ref(v___x_987_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_978_);
v___x_997_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v_c_995_);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__8);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_MessageData_note(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_msg_977_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
return v___x_1003_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1038_; 
v_val_1004_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1006_ = v___x_996_;
v_isShared_1007_ = v_isSharedCheck_1038_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_val_1004_);
lean_dec(v___x_996_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1038_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v_moduleNames_1009_; lean_object* v_mod_1010_; uint8_t v___x_1011_; 
v___x_1008_ = l_Lean_Environment_header(v_env_983_);
lean_dec_ref(v_env_983_);
v_moduleNames_1009_ = lean_ctor_get(v___x_1008_, 4);
lean_inc_ref(v_moduleNames_1009_);
lean_dec_ref(v___x_1008_);
v_mod_1010_ = lean_array_get(v___x_981_, v_moduleNames_1009_, v_val_1004_);
lean_dec(v_val_1004_);
lean_dec_ref(v_moduleNames_1009_);
v___x_1011_ = l_Lean_isPrivateName(v_declHint_978_);
lean_dec(v_declHint_978_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__10);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_c_995_);
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__12);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofName(v_mod_1010_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__14);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_note(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_msg_977_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1021_);
v___x_1023_ = v___x_1006_;
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
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1025_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__6);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v_c_995_);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__16);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_MessageData_ofName(v_mod_1010_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___closed__18);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_MessageData_note(v___x_1032_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_msg_977_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1034_);
v___x_1036_ = v___x_1006_;
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
lean_object* v___x_1039_; 
lean_dec_ref(v_env_983_);
lean_dec(v_declHint_978_);
v___x_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1039_, 0, v_msg_977_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg___boxed(lean_object* v_msg_1040_, lean_object* v_declHint_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1040_, v_declHint_1041_, v___y_1042_);
lean_dec(v___y_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(lean_object* v_msg_1045_, lean_object* v_declHint_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1062_; 
v___x_1052_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1045_, v_declHint_1046_, v___y_1050_);
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1062_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1057_ = l_Lean_unknownIdentifierMessageTag;
v___x_1058_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14___boxed(lean_object* v_msg_1063_, lean_object* v_declHint_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1063_, v_declHint_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(lean_object* v_ref_1071_, lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14(v_msg_1072_, v_declHint_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1071_, v_a_1080_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg___boxed(lean_object* v_ref_1082_, lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1082_, v_msg_1083_, v_declHint_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v_ref_1082_);
return v_res_1090_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1093_ = l_Lean_stringToMessageData(v___x_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1097_, lean_object* v_constName_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1104_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1105_ = 0;
lean_inc(v_constName_1098_);
v___x_1106_ = l_Lean_MessageData_ofConstName(v_constName_1098_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1104_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1097_, v___x_1109_, v_constName_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1111_, lean_object* v_constName_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1111_, v_constName_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v_ref_1111_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_ref_1125_; lean_object* v___x_1126_; 
v_ref_1125_ = lean_ctor_get(v___y_1122_, 2);
v___x_1126_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1125_, v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_st_ref_get(v___y_1138_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1142_ = 0;
lean_inc(v_constName_1134_);
v___x_1143_ = l_Lean_Environment_find_x3f(v_env_1141_, v_constName_1134_, v___x_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1144_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_constName_1134_);
v_val_1145_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_val_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 0);
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_val_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1168_ = l_Lean_stringToMessageData(v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1169_, lean_object* v_nParams_1170_, lean_object* v_belowName_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1169_);
v___x_1178_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1169_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
if (lean_obj_tag(v_a_1179_) == 7)
{
lean_object* v_val_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1297_; 
v_val_1180_ = lean_ctor_get(v_a_1179_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1182_ = v_a_1179_;
v_isShared_1183_ = v_isSharedCheck_1297_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_val_1180_);
lean_dec(v_a_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1297_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_toConstantVal_1184_; lean_object* v_numMotives_1185_; lean_object* v_numMinors_1186_; lean_object* v_levelParams_1187_; lean_object* v_type_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_toConstantVal_1184_ = lean_ctor_get(v_val_1180_, 0);
lean_inc_ref(v_toConstantVal_1184_);
v_numMotives_1185_ = lean_ctor_get(v_val_1180_, 4);
lean_inc(v_numMotives_1185_);
v_numMinors_1186_ = lean_ctor_get(v_val_1180_, 5);
lean_inc(v_numMinors_1186_);
lean_dec_ref(v_val_1180_);
v_levelParams_1187_ = lean_ctor_get(v_toConstantVal_1184_, 1);
lean_inc_n(v_levelParams_1187_, 2);
v_type_1188_ = lean_ctor_get(v_toConstantVal_1184_, 2);
lean_inc_ref(v_type_1188_);
lean_dec_ref(v_toConstantVal_1184_);
v___x_1189_ = lean_box(0);
v___x_1190_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1187_, v___x_1189_);
if (lean_obj_tag(v___x_1190_) == 1)
{
lean_object* v_head_1191_; lean_object* v_tail_1192_; lean_object* v___f_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; 
v_head_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_head_1191_);
v_tail_1192_ = lean_ctor_get(v___x_1190_, 1);
lean_inc(v_tail_1192_);
lean_dec_ref_known(v___x_1190_, 2);
v___f_1193_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1193_, 0, v_nParams_1170_);
lean_closure_set(v___f_1193_, 1, v_numMotives_1185_);
lean_closure_set(v___f_1193_, 2, v_numMinors_1186_);
lean_closure_set(v___f_1193_, 3, v___x_1177_);
lean_closure_set(v___f_1193_, 4, v_head_1191_);
lean_closure_set(v___f_1193_, 5, v_tail_1192_);
lean_closure_set(v___f_1193_, 6, v_recName_1169_);
lean_closure_set(v___f_1193_, 7, v_belowName_1171_);
lean_closure_set(v___f_1193_, 8, v_levelParams_1187_);
v___x_1194_ = 0;
v___x_1195_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1188_, v___f_1193_, v___x_1194_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_n(v_a_1196_, 2);
lean_dec_ref_known(v___x_1195_, 1);
if (v_isShared_1183_ == 0)
{
lean_ctor_set_tag(v___x_1182_, 1);
lean_ctor_set(v___x_1182_, 0, v_a_1196_);
v___x_1198_ = v___x_1182_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1196_);
v___x_1198_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_addDecl(v___x_1198_, v___x_1194_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_toConstantVal_1200_; lean_object* v_name_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref_known(v___x_1199_, 1);
v_toConstantVal_1200_ = lean_ctor_get(v_a_1196_, 0);
lean_inc_ref(v_toConstantVal_1200_);
lean_dec(v_a_1196_);
v_name_1201_ = lean_ctor_get(v_toConstantVal_1200_, 0);
lean_inc_n(v_name_1201_, 2);
lean_dec_ref(v_toConstantVal_1200_);
v___x_1202_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1201_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1202_, 0);
lean_dec(v_unused_1281_);
v___x_1204_ = v___x_1202_;
v_isShared_1205_ = v_isSharedCheck_1280_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v___x_1202_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1280_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v_env_1207_; lean_object* v_nextMacroScope_1208_; lean_object* v_ngen_1209_; lean_object* v_auxDeclNGen_1210_; lean_object* v_traceState_1211_; lean_object* v_recordedDeps_1212_; lean_object* v_messages_1213_; lean_object* v_infoState_1214_; lean_object* v_snapshotTasks_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1278_; 
v___x_1206_ = lean_st_ref_take(v_a_1175_);
v_env_1207_ = lean_ctor_get(v___x_1206_, 0);
v_nextMacroScope_1208_ = lean_ctor_get(v___x_1206_, 1);
v_ngen_1209_ = lean_ctor_get(v___x_1206_, 2);
v_auxDeclNGen_1210_ = lean_ctor_get(v___x_1206_, 3);
v_traceState_1211_ = lean_ctor_get(v___x_1206_, 4);
v_recordedDeps_1212_ = lean_ctor_get(v___x_1206_, 6);
v_messages_1213_ = lean_ctor_get(v___x_1206_, 7);
v_infoState_1214_ = lean_ctor_get(v___x_1206_, 8);
v_snapshotTasks_1215_ = lean_ctor_get(v___x_1206_, 9);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1206_, 5);
lean_dec(v_unused_1279_);
v___x_1217_ = v___x_1206_;
v_isShared_1218_ = v_isSharedCheck_1278_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_snapshotTasks_1215_);
lean_inc(v_infoState_1214_);
lean_inc(v_messages_1213_);
lean_inc(v_recordedDeps_1212_);
lean_inc(v_traceState_1211_);
lean_inc(v_auxDeclNGen_1210_);
lean_inc(v_ngen_1209_);
lean_inc(v_nextMacroScope_1208_);
lean_inc(v_env_1207_);
lean_dec(v___x_1206_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1278_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_inc(v_name_1201_);
v___x_1219_ = l_Lean_markAuxRecursor(v_env_1207_, v_name_1201_);
v___x_1220_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 5, v___x_1220_);
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_nextMacroScope_1208_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_ngen_1209_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_auxDeclNGen_1210_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_traceState_1211_);
lean_ctor_set(v_reuseFailAlloc_1277_, 5, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1277_, 6, v_recordedDeps_1212_);
lean_ctor_set(v_reuseFailAlloc_1277_, 7, v_messages_1213_);
lean_ctor_set(v_reuseFailAlloc_1277_, 8, v_infoState_1214_);
lean_ctor_set(v_reuseFailAlloc_1277_, 9, v_snapshotTasks_1215_);
v___x_1222_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_mctx_1225_; lean_object* v_zetaDeltaFVarIds_1226_; lean_object* v_postponed_1227_; lean_object* v_diag_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1275_; 
v___x_1223_ = lean_st_ref_put(v_a_1175_, v___x_1222_);
v___x_1224_ = lean_st_ref_take(v_a_1173_);
v_mctx_1225_ = lean_ctor_get(v___x_1224_, 0);
v_zetaDeltaFVarIds_1226_ = lean_ctor_get(v___x_1224_, 2);
v_postponed_1227_ = lean_ctor_get(v___x_1224_, 3);
v_diag_1228_ = lean_ctor_get(v___x_1224_, 4);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; 
v_unused_1276_ = lean_ctor_get(v___x_1224_, 1);
lean_dec(v_unused_1276_);
v___x_1230_ = v___x_1224_;
v_isShared_1231_ = v_isSharedCheck_1275_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_diag_1228_);
lean_inc(v_postponed_1227_);
lean_inc(v_zetaDeltaFVarIds_1226_);
lean_inc(v_mctx_1225_);
lean_dec(v___x_1224_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1275_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__5);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_mctx_1225_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_zetaDeltaFVarIds_1226_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_postponed_1227_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_diag_1228_);
v___x_1234_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_env_1237_; lean_object* v_nextMacroScope_1238_; lean_object* v_ngen_1239_; lean_object* v_auxDeclNGen_1240_; lean_object* v_traceState_1241_; lean_object* v_recordedDeps_1242_; lean_object* v_messages_1243_; lean_object* v_infoState_1244_; lean_object* v_snapshotTasks_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1272_; 
v___x_1235_ = lean_st_ref_put(v_a_1173_, v___x_1234_);
v___x_1236_ = lean_st_ref_take(v_a_1175_);
v_env_1237_ = lean_ctor_get(v___x_1236_, 0);
v_nextMacroScope_1238_ = lean_ctor_get(v___x_1236_, 1);
v_ngen_1239_ = lean_ctor_get(v___x_1236_, 2);
v_auxDeclNGen_1240_ = lean_ctor_get(v___x_1236_, 3);
v_traceState_1241_ = lean_ctor_get(v___x_1236_, 4);
v_recordedDeps_1242_ = lean_ctor_get(v___x_1236_, 6);
v_messages_1243_ = lean_ctor_get(v___x_1236_, 7);
v_infoState_1244_ = lean_ctor_get(v___x_1236_, 8);
v_snapshotTasks_1245_ = lean_ctor_get(v___x_1236_, 9);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1236_, 5);
lean_dec(v_unused_1273_);
v___x_1247_ = v___x_1236_;
v_isShared_1248_ = v_isSharedCheck_1272_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_snapshotTasks_1245_);
lean_inc(v_infoState_1244_);
lean_inc(v_messages_1243_);
lean_inc(v_recordedDeps_1242_);
lean_inc(v_traceState_1241_);
lean_inc(v_auxDeclNGen_1240_);
lean_inc(v_ngen_1239_);
lean_inc(v_nextMacroScope_1238_);
lean_inc(v_env_1237_);
lean_dec(v___x_1236_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1272_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = l_Lean_addProtected(v_env_1237_, v_name_1201_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 5, v___x_1220_);
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_nextMacroScope_1238_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_ngen_1239_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_auxDeclNGen_1240_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_traceState_1241_);
lean_ctor_set(v_reuseFailAlloc_1271_, 5, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1271_, 6, v_recordedDeps_1242_);
lean_ctor_set(v_reuseFailAlloc_1271_, 7, v_messages_1243_);
lean_ctor_set(v_reuseFailAlloc_1271_, 8, v_infoState_1244_);
lean_ctor_set(v_reuseFailAlloc_1271_, 9, v_snapshotTasks_1245_);
v___x_1251_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_mctx_1254_; lean_object* v_zetaDeltaFVarIds_1255_; lean_object* v_postponed_1256_; lean_object* v_diag_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1269_; 
v___x_1252_ = lean_st_ref_put(v_a_1175_, v___x_1251_);
v___x_1253_ = lean_st_ref_take(v_a_1173_);
v_mctx_1254_ = lean_ctor_get(v___x_1253_, 0);
v_zetaDeltaFVarIds_1255_ = lean_ctor_get(v___x_1253_, 2);
v_postponed_1256_ = lean_ctor_get(v___x_1253_, 3);
v_diag_1257_ = lean_ctor_get(v___x_1253_, 4);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1253_, 1);
lean_dec(v_unused_1270_);
v___x_1259_ = v___x_1253_;
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_diag_1257_);
lean_inc(v_postponed_1256_);
lean_inc(v_zetaDeltaFVarIds_1255_);
lean_inc(v_mctx_1254_);
lean_dec(v___x_1253_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1269_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_box(0);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1232_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_mctx_1254_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_zetaDeltaFVarIds_1255_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_postponed_1256_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_diag_1257_);
v___x_1263_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1264_ = lean_st_ref_put(v_a_1173_, v___x_1263_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1261_);
v___x_1266_ = v___x_1204_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
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
lean_dec(v_a_1196_);
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1182_);
v_a_1283_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1195_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1195_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec(v___x_1190_);
lean_dec_ref(v_type_1188_);
lean_dec(v_levelParams_1187_);
lean_dec(v_numMinors_1186_);
lean_dec(v_numMotives_1185_);
lean_del_object(v___x_1182_);
lean_dec(v_belowName_1171_);
lean_dec(v_nParams_1170_);
v___x_1291_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1292_ = l_Lean_MessageData_ofName(v_recName_1169_);
v___x_1293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1291_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1293_);
lean_ctor_set(v___x_1295_, 1, v___x_1294_);
v___x_1296_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1295_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1296_;
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec(v_a_1179_);
lean_dec(v_belowName_1171_);
lean_dec(v_nParams_1170_);
v___x_1298_ = l_Lean_MessageData_ofName(v_recName_1169_);
v___x_1299_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1300_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1301_;
}
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_belowName_1171_);
lean_dec(v_nParams_1170_);
lean_dec(v_recName_1169_);
v_a_1302_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1178_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1178_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1310_, lean_object* v_nParams_1311_, lean_object* v_belowName_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1310_, v_nParams_1311_, v_belowName_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1327_, lean_object* v_msg_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1327_, v_msg_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8_spec__11(lean_object* v_00_u03b2_1335_){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg(){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg___boxed(lean_object* v___dummy_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8___redArg();
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__8(lean_object* v_00_u03b2_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1343_, lean_object* v_constName_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_constName_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1351_, v_constName_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1359_, uint8_t v_s_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1359_, v_s_1360_, v___y_1362_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1367_, lean_object* v_s_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_s_boxed_1374_; lean_object* v_res_1375_; 
v_s_boxed_1374_ = lean_unbox(v_s_1368_);
v_res_1375_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1367_, v_s_boxed_1374_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1376_, lean_object* v_ref_1377_, lean_object* v_constName_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1377_, v_constName_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_ref_1386_, lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1385_, v_ref_1386_, v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v_ref_1386_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(lean_object* v_00_u03b1_1394_, lean_object* v_ref_1395_, lean_object* v_msg_1396_, lean_object* v_declHint_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___redArg(v_ref_1395_, v_msg_1396_, v_declHint_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_ref_1405_, lean_object* v_msg_1406_, lean_object* v_declHint_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12(v_00_u03b1_1404_, v_ref_1405_, v_msg_1406_, v_declHint_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v_ref_1405_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___redArg(v_msg_1414_, v_declHint_1415_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_1422_, lean_object* v_declHint_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__14_spec__15(v_msg_1422_, v_declHint_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(lean_object* v_00_u03b1_1430_, lean_object* v_ref_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___redArg(v_ref_1431_, v_msg_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_msg_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__12_spec__15(v_00_u03b1_1439_, v_ref_1440_, v_msg_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v_ref_1440_);
return v_res_1447_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1448_ = lean_unsigned_to_nat(32u);
v___x_1449_ = lean_mk_empty_array_with_capacity(v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1451_ = ((size_t)5ULL);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = lean_unsigned_to_nat(32u);
v___x_1454_ = lean_mk_empty_array_with_capacity(v___x_1453_);
v___x_1455_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1456_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
lean_ctor_set(v___x_1456_, 1, v___x_1454_);
lean_ctor_set(v___x_1456_, 2, v___x_1452_);
lean_ctor_set(v___x_1456_, 3, v___x_1452_);
lean_ctor_set_usize(v___x_1456_, 4, v___x_1451_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; lean_object* v_traceState_1460_; lean_object* v_traces_1461_; lean_object* v___x_1462_; lean_object* v_traceState_1463_; lean_object* v_env_1464_; lean_object* v_nextMacroScope_1465_; lean_object* v_ngen_1466_; lean_object* v_auxDeclNGen_1467_; lean_object* v_cache_1468_; lean_object* v_recordedDeps_1469_; lean_object* v_messages_1470_; lean_object* v_infoState_1471_; lean_object* v_snapshotTasks_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1491_; 
v___x_1459_ = lean_st_ref_get(v___y_1457_);
v_traceState_1460_ = lean_ctor_get(v___x_1459_, 4);
lean_inc_ref(v_traceState_1460_);
lean_dec(v___x_1459_);
v_traces_1461_ = lean_ctor_get(v_traceState_1460_, 0);
lean_inc_ref(v_traces_1461_);
lean_dec_ref(v_traceState_1460_);
v___x_1462_ = lean_st_ref_take(v___y_1457_);
v_traceState_1463_ = lean_ctor_get(v___x_1462_, 4);
v_env_1464_ = lean_ctor_get(v___x_1462_, 0);
v_nextMacroScope_1465_ = lean_ctor_get(v___x_1462_, 1);
v_ngen_1466_ = lean_ctor_get(v___x_1462_, 2);
v_auxDeclNGen_1467_ = lean_ctor_get(v___x_1462_, 3);
v_cache_1468_ = lean_ctor_get(v___x_1462_, 5);
v_recordedDeps_1469_ = lean_ctor_get(v___x_1462_, 6);
v_messages_1470_ = lean_ctor_get(v___x_1462_, 7);
v_infoState_1471_ = lean_ctor_get(v___x_1462_, 8);
v_snapshotTasks_1472_ = lean_ctor_get(v___x_1462_, 9);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1474_ = v___x_1462_;
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snapshotTasks_1472_);
lean_inc(v_infoState_1471_);
lean_inc(v_messages_1470_);
lean_inc(v_recordedDeps_1469_);
lean_inc(v_cache_1468_);
lean_inc(v_traceState_1463_);
lean_inc(v_auxDeclNGen_1467_);
lean_inc(v_ngen_1466_);
lean_inc(v_nextMacroScope_1465_);
lean_inc(v_env_1464_);
lean_dec(v___x_1462_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1491_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
uint64_t v_tid_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1489_; 
v_tid_1476_ = lean_ctor_get_uint64(v_traceState_1463_, sizeof(void*)*1);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_traceState_1463_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; 
v_unused_1490_ = lean_ctor_get(v_traceState_1463_, 0);
lean_dec(v_unused_1490_);
v___x_1478_ = v_traceState_1463_;
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
else
{
lean_dec(v_traceState_1463_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1489_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1480_);
v___x_1482_ = v___x_1478_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1480_);
lean_ctor_set_uint64(v_reuseFailAlloc_1488_, sizeof(void*)*1, v_tid_1476_);
v___x_1482_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v___x_1482_);
v___x_1484_ = v___x_1474_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_env_1464_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_nextMacroScope_1465_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_ngen_1466_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_auxDeclNGen_1467_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1487_, 5, v_cache_1468_);
lean_ctor_set(v_reuseFailAlloc_1487_, 6, v_recordedDeps_1469_);
lean_ctor_set(v_reuseFailAlloc_1487_, 7, v_messages_1470_);
lean_ctor_set(v_reuseFailAlloc_1487_, 8, v_infoState_1471_);
lean_ctor_set(v_reuseFailAlloc_1487_, 9, v_snapshotTasks_1472_);
v___x_1484_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = lean_st_ref_put(v___y_1457_, v___x_1484_);
v___x_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_traces_1461_);
return v___x_1486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1492_);
lean_dec(v___y_1492_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1507_, lean_object* v_opt_1508_){
_start:
{
lean_object* v_name_1509_; lean_object* v_defValue_1510_; lean_object* v_map_1511_; lean_object* v___x_1512_; 
v_name_1509_ = lean_ctor_get(v_opt_1508_, 0);
v_defValue_1510_ = lean_ctor_get(v_opt_1508_, 1);
v_map_1511_ = lean_ctor_get(v_opts_1507_, 0);
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1511_, v_name_1509_);
if (lean_obj_tag(v___x_1512_) == 0)
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_unbox(v_defValue_1510_);
return v___x_1513_;
}
else
{
lean_object* v_val_1514_; 
v_val_1514_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1512_, 1);
if (lean_obj_tag(v_val_1514_) == 1)
{
uint8_t v_v_1515_; 
v_v_1515_ = lean_ctor_get_uint8(v_val_1514_, 0);
lean_dec_ref_known(v_val_1514_, 0);
return v_v_1515_;
}
else
{
uint8_t v___x_1516_; 
lean_dec(v_val_1514_);
v___x_1516_ = lean_unbox(v_defValue_1510_);
return v___x_1516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1517_, lean_object* v_opt_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1517_, v_opt_1518_);
lean_dec_ref(v_opt_1518_);
lean_dec_ref(v_opts_1517_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l_Lean_MessageData_ofName(v_indName_1521_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_mkBelow___lam__0(v_indName_1530_, v_x_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_x_1531_);
return v_res_1537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1538_){
_start:
{
if (lean_obj_tag(v_e_1538_) == 0)
{
uint8_t v___x_1539_; 
v___x_1539_ = 2;
return v___x_1539_;
}
else
{
uint8_t v___x_1540_; 
v___x_1540_ = 0;
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1541_){
_start:
{
uint8_t v_res_1542_; lean_object* v_r_1543_; 
v_res_1542_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1541_);
lean_dec_ref(v_e_1541_);
v_r_1543_ = lean_box(v_res_1542_);
return v_r_1543_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1544_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
v_a_1546_ = lean_ctor_get(v_x_1544_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v_x_1544_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v_x_1544_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
lean_ctor_set_tag(v___x_1548_, 1);
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_a_1554_ = lean_ctor_get(v_x_1544_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_x_1544_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v_x_1544_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v_x_1544_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set_tag(v___x_1556_, 0);
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1565_, lean_object* v_opt_1566_){
_start:
{
lean_object* v_name_1567_; lean_object* v_defValue_1568_; lean_object* v_map_1569_; lean_object* v___x_1570_; 
v_name_1567_ = lean_ctor_get(v_opt_1566_, 0);
v_defValue_1568_ = lean_ctor_get(v_opt_1566_, 1);
v_map_1569_ = lean_ctor_get(v_opts_1565_, 0);
v___x_1570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1569_, v_name_1567_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_inc(v_defValue_1568_);
return v_defValue_1568_;
}
else
{
lean_object* v_val_1571_; 
v_val_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v___x_1570_, 1);
if (lean_obj_tag(v_val_1571_) == 3)
{
lean_object* v_v_1572_; 
v_v_1572_ = lean_ctor_get(v_val_1571_, 0);
lean_inc(v_v_1572_);
lean_dec_ref_known(v_val_1571_, 1);
return v_v_1572_;
}
else
{
lean_dec(v_val_1571_);
lean_inc(v_defValue_1568_);
return v_defValue_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1573_, lean_object* v_opt_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1573_, v_opt_1574_);
lean_dec_ref(v_opt_1574_);
lean_dec_ref(v_opts_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1576_, size_t v_i_1577_, lean_object* v_bs_1578_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_lt(v_i_1577_, v_sz_1576_);
if (v___x_1579_ == 0)
{
return v_bs_1578_;
}
else
{
lean_object* v_v_1580_; lean_object* v_msg_1581_; lean_object* v___x_1582_; lean_object* v_bs_x27_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v_v_1580_ = lean_array_uget_borrowed(v_bs_1578_, v_i_1577_);
v_msg_1581_ = lean_ctor_get(v_v_1580_, 1);
lean_inc_ref(v_msg_1581_);
v___x_1582_ = lean_unsigned_to_nat(0u);
v_bs_x27_1583_ = lean_array_uset(v_bs_1578_, v_i_1577_, v___x_1582_);
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = lean_usize_add(v_i_1577_, v___x_1584_);
v___x_1586_ = lean_array_uset(v_bs_x27_1583_, v_i_1577_, v_msg_1581_);
v_i_1577_ = v___x_1585_;
v_bs_1578_ = v___x_1586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1588_, lean_object* v_i_1589_, lean_object* v_bs_1590_){
_start:
{
size_t v_sz_boxed_1591_; size_t v_i_boxed_1592_; lean_object* v_res_1593_; 
v_sz_boxed_1591_ = lean_unbox_usize(v_sz_1588_);
lean_dec(v_sz_1588_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1589_);
lean_dec(v_i_1589_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1591_, v_i_boxed_1592_, v_bs_1590_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1594_, lean_object* v_data_1595_, lean_object* v_ref_1596_, lean_object* v_msg_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_toCold_1603_; lean_object* v_currRecDepth_1604_; lean_object* v_ref_1605_; uint16_t v_optionFlags_1606_; uint8_t v_suppressElabErrors_1607_; uint8_t v_checkDeprecated_1608_; uint8_t v_isRecordingDeps_1609_; lean_object* v_ref_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v_traceState_1613_; lean_object* v_traces_1614_; lean_object* v___x_1615_; size_t v_sz_1616_; size_t v___x_1617_; lean_object* v___x_1618_; lean_object* v_msg_1619_; lean_object* v___x_1620_; lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1659_; 
v_toCold_1603_ = lean_ctor_get(v___y_1600_, 0);
v_currRecDepth_1604_ = lean_ctor_get(v___y_1600_, 1);
v_ref_1605_ = lean_ctor_get(v___y_1600_, 2);
v_optionFlags_1606_ = lean_ctor_get_uint16(v___y_1600_, sizeof(void*)*3);
v_suppressElabErrors_1607_ = lean_ctor_get_uint8(v___y_1600_, sizeof(void*)*3 + 2);
v_checkDeprecated_1608_ = lean_ctor_get_uint8(v___y_1600_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1609_ = lean_ctor_get_uint8(v___y_1600_, sizeof(void*)*3 + 4);
v_ref_1610_ = l_Lean_replaceRef(v_ref_1596_, v_ref_1605_);
lean_inc(v_currRecDepth_1604_);
lean_inc_ref(v_toCold_1603_);
v___x_1611_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1611_, 0, v_toCold_1603_);
lean_ctor_set(v___x_1611_, 1, v_currRecDepth_1604_);
lean_ctor_set(v___x_1611_, 2, v_ref_1610_);
lean_ctor_set_uint16(v___x_1611_, sizeof(void*)*3, v_optionFlags_1606_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 2, v_suppressElabErrors_1607_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 3, v_checkDeprecated_1608_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 4, v_isRecordingDeps_1609_);
v___x_1612_ = lean_st_ref_get(v___y_1601_);
v_traceState_1613_ = lean_ctor_get(v___x_1612_, 4);
lean_inc_ref(v_traceState_1613_);
lean_dec(v___x_1612_);
v_traces_1614_ = lean_ctor_get(v_traceState_1613_, 0);
lean_inc_ref(v_traces_1614_);
lean_dec_ref(v_traceState_1613_);
v___x_1615_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1614_);
lean_dec_ref(v_traces_1614_);
v_sz_1616_ = lean_array_size(v___x_1615_);
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1616_, v___x_1617_, v___x_1615_);
v_msg_1619_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1619_, 0, v_data_1595_);
lean_ctor_set(v_msg_1619_, 1, v_msg_1597_);
lean_ctor_set(v_msg_1619_, 2, v___x_1618_);
v___x_1620_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1619_, v___y_1598_, v___y_1599_, v___x_1611_, v___y_1601_);
lean_dec_ref_known(v___x_1611_, 3);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1659_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1659_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v_traceState_1626_; lean_object* v_env_1627_; lean_object* v_nextMacroScope_1628_; lean_object* v_ngen_1629_; lean_object* v_auxDeclNGen_1630_; lean_object* v_cache_1631_; lean_object* v_recordedDeps_1632_; lean_object* v_messages_1633_; lean_object* v_infoState_1634_; lean_object* v_snapshotTasks_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1658_; 
v___x_1625_ = lean_st_ref_take(v___y_1601_);
v_traceState_1626_ = lean_ctor_get(v___x_1625_, 4);
v_env_1627_ = lean_ctor_get(v___x_1625_, 0);
v_nextMacroScope_1628_ = lean_ctor_get(v___x_1625_, 1);
v_ngen_1629_ = lean_ctor_get(v___x_1625_, 2);
v_auxDeclNGen_1630_ = lean_ctor_get(v___x_1625_, 3);
v_cache_1631_ = lean_ctor_get(v___x_1625_, 5);
v_recordedDeps_1632_ = lean_ctor_get(v___x_1625_, 6);
v_messages_1633_ = lean_ctor_get(v___x_1625_, 7);
v_infoState_1634_ = lean_ctor_get(v___x_1625_, 8);
v_snapshotTasks_1635_ = lean_ctor_get(v___x_1625_, 9);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1637_ = v___x_1625_;
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_snapshotTasks_1635_);
lean_inc(v_infoState_1634_);
lean_inc(v_messages_1633_);
lean_inc(v_recordedDeps_1632_);
lean_inc(v_cache_1631_);
lean_inc(v_traceState_1626_);
lean_inc(v_auxDeclNGen_1630_);
lean_inc(v_ngen_1629_);
lean_inc(v_nextMacroScope_1628_);
lean_inc(v_env_1627_);
lean_dec(v___x_1625_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1658_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
uint64_t v_tid_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1656_; 
v_tid_1639_ = lean_ctor_get_uint64(v_traceState_1626_, sizeof(void*)*1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_traceState_1626_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v_traceState_1626_, 0);
lean_dec(v_unused_1657_);
v___x_1641_ = v_traceState_1626_;
v_isShared_1642_ = v_isSharedCheck_1656_;
goto v_resetjp_1640_;
}
else
{
lean_dec(v_traceState_1626_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1656_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_ref_1596_);
lean_ctor_set(v___x_1644_, 1, v_a_1621_);
v___x_1645_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1594_, v___x_1644_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1645_);
v___x_1647_ = v___x_1641_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1645_);
lean_ctor_set_uint64(v_reuseFailAlloc_1655_, sizeof(void*)*1, v_tid_1639_);
v___x_1647_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v___x_1647_);
v___x_1649_ = v___x_1637_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_env_1627_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_nextMacroScope_1628_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_ngen_1629_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_auxDeclNGen_1630_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1654_, 5, v_cache_1631_);
lean_ctor_set(v_reuseFailAlloc_1654_, 6, v_recordedDeps_1632_);
lean_ctor_set(v_reuseFailAlloc_1654_, 7, v_messages_1633_);
lean_ctor_set(v_reuseFailAlloc_1654_, 8, v_infoState_1634_);
lean_ctor_set(v_reuseFailAlloc_1654_, 9, v_snapshotTasks_1635_);
v___x_1649_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_st_ref_put(v___y_1601_, v___x_1649_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1643_);
v___x_1652_ = v___x_1623_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1643_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1660_, lean_object* v_data_1661_, lean_object* v_ref_1662_, lean_object* v_msg_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1660_, v_data_1661_, v_ref_1662_, v_msg_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1669_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1670_; double v___x_1671_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_float_of_nat(v___x_1670_);
return v___x_1671_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1675_; double v___x_1676_; 
v___x_1675_ = lean_unsigned_to_nat(1000u);
v___x_1676_ = lean_float_of_nat(v___x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1677_, uint8_t v_collapsed_1678_, lean_object* v_tag_1679_, lean_object* v_opts_1680_, uint8_t v_clsEnabled_1681_, lean_object* v_oldTraces_1682_, lean_object* v_msg_1683_, lean_object* v_resStartStop_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_fst_1690_; lean_object* v_snd_1691_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v_data_1695_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___y_1703_; lean_object* v_a_1704_; uint8_t v___y_1719_; double v___y_1751_; 
v_fst_1690_ = lean_ctor_get(v_resStartStop_1684_, 0);
lean_inc(v_fst_1690_);
v_snd_1691_ = lean_ctor_get(v_resStartStop_1684_, 1);
lean_inc(v_snd_1691_);
lean_dec_ref(v_resStartStop_1684_);
v_fst_1698_ = lean_ctor_get(v_snd_1691_, 0);
lean_inc(v_fst_1698_);
v_snd_1699_ = lean_ctor_get(v_snd_1691_, 1);
lean_inc(v_snd_1699_);
lean_dec(v_snd_1691_);
v___x_1700_ = l_Lean_trace_profiler;
v___x_1701_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1680_, v___x_1700_);
if (v___x_1701_ == 0)
{
v___y_1719_ = v___x_1701_;
goto v___jp_1718_;
}
else
{
lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1757_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1680_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; double v___x_1760_; double v___x_1761_; double v___x_1762_; 
v___x_1758_ = l_Lean_trace_profiler_threshold;
v___x_1759_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1680_, v___x_1758_);
v___x_1760_ = lean_float_of_nat(v___x_1759_);
v___x_1761_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1762_ = lean_float_div(v___x_1760_, v___x_1761_);
v___y_1751_ = v___x_1762_;
goto v___jp_1750_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; double v___x_1765_; 
v___x_1763_ = l_Lean_trace_profiler_threshold;
v___x_1764_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1680_, v___x_1763_);
v___x_1765_ = lean_float_of_nat(v___x_1764_);
v___y_1751_ = v___x_1765_;
goto v___jp_1750_;
}
}
v___jp_1692_:
{
lean_object* v___x_1696_; 
lean_inc(v___y_1694_);
v___x_1696_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1682_, v_data_1695_, v___y_1694_, v___y_1693_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref_known(v___x_1696_, 1);
v___x_1697_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1690_);
return v___x_1697_;
}
else
{
lean_dec(v_fst_1690_);
return v___x_1696_;
}
}
v___jp_1702_:
{
uint8_t v_result_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; double v___x_1708_; lean_object* v_data_1709_; 
v_result_1705_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1690_);
v___x_1706_ = lean_box(v_result_1705_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
v___x_1708_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1679_);
lean_inc_ref(v___x_1707_);
lean_inc(v_cls_1677_);
v_data_1709_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1709_, 0, v_cls_1677_);
lean_ctor_set(v_data_1709_, 1, v___x_1707_);
lean_ctor_set(v_data_1709_, 2, v_tag_1679_);
lean_ctor_set_float(v_data_1709_, sizeof(void*)*3, v___x_1708_);
lean_ctor_set_float(v_data_1709_, sizeof(void*)*3 + 8, v___x_1708_);
lean_ctor_set_uint8(v_data_1709_, sizeof(void*)*3 + 16, v_collapsed_1678_);
if (v___x_1701_ == 0)
{
lean_dec_ref_known(v___x_1707_, 1);
lean_dec(v_snd_1699_);
lean_dec(v_fst_1698_);
lean_dec_ref(v_tag_1679_);
lean_dec(v_cls_1677_);
v___y_1693_ = v_a_1704_;
v___y_1694_ = v___y_1703_;
v_data_1695_ = v_data_1709_;
goto v___jp_1692_;
}
else
{
lean_object* v_data_1710_; double v___x_1711_; double v___x_1712_; 
lean_dec_ref_known(v_data_1709_, 3);
v_data_1710_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1710_, 0, v_cls_1677_);
lean_ctor_set(v_data_1710_, 1, v___x_1707_);
lean_ctor_set(v_data_1710_, 2, v_tag_1679_);
v___x_1711_ = lean_unbox_float(v_fst_1698_);
lean_dec(v_fst_1698_);
lean_ctor_set_float(v_data_1710_, sizeof(void*)*3, v___x_1711_);
v___x_1712_ = lean_unbox_float(v_snd_1699_);
lean_dec(v_snd_1699_);
lean_ctor_set_float(v_data_1710_, sizeof(void*)*3 + 8, v___x_1712_);
lean_ctor_set_uint8(v_data_1710_, sizeof(void*)*3 + 16, v_collapsed_1678_);
v___y_1693_ = v_a_1704_;
v___y_1694_ = v___y_1703_;
v_data_1695_ = v_data_1710_;
goto v___jp_1692_;
}
}
v___jp_1713_:
{
lean_object* v_ref_1714_; lean_object* v___x_1715_; 
v_ref_1714_ = lean_ctor_get(v___y_1687_, 2);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v_fst_1690_);
v___x_1715_ = lean_apply_6(v_msg_1683_, v_fst_1690_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, lean_box(0));
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___y_1703_ = v_ref_1714_;
v_a_1704_ = v_a_1716_;
goto v___jp_1702_;
}
else
{
lean_object* v___x_1717_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1717_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1703_ = v_ref_1714_;
v_a_1704_ = v___x_1717_;
goto v___jp_1702_;
}
}
v___jp_1718_:
{
if (v_clsEnabled_1681_ == 0)
{
if (v___y_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v_traceState_1721_; lean_object* v_env_1722_; lean_object* v_nextMacroScope_1723_; lean_object* v_ngen_1724_; lean_object* v_auxDeclNGen_1725_; lean_object* v_cache_1726_; lean_object* v_recordedDeps_1727_; lean_object* v_messages_1728_; lean_object* v_infoState_1729_; lean_object* v_snapshotTasks_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_snd_1699_);
lean_dec(v_fst_1698_);
lean_dec_ref(v_msg_1683_);
lean_dec_ref(v_tag_1679_);
lean_dec(v_cls_1677_);
v___x_1720_ = lean_st_ref_take(v___y_1688_);
v_traceState_1721_ = lean_ctor_get(v___x_1720_, 4);
v_env_1722_ = lean_ctor_get(v___x_1720_, 0);
v_nextMacroScope_1723_ = lean_ctor_get(v___x_1720_, 1);
v_ngen_1724_ = lean_ctor_get(v___x_1720_, 2);
v_auxDeclNGen_1725_ = lean_ctor_get(v___x_1720_, 3);
v_cache_1726_ = lean_ctor_get(v___x_1720_, 5);
v_recordedDeps_1727_ = lean_ctor_get(v___x_1720_, 6);
v_messages_1728_ = lean_ctor_get(v___x_1720_, 7);
v_infoState_1729_ = lean_ctor_get(v___x_1720_, 8);
v_snapshotTasks_1730_ = lean_ctor_get(v___x_1720_, 9);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1732_ = v___x_1720_;
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_snapshotTasks_1730_);
lean_inc(v_infoState_1729_);
lean_inc(v_messages_1728_);
lean_inc(v_recordedDeps_1727_);
lean_inc(v_cache_1726_);
lean_inc(v_traceState_1721_);
lean_inc(v_auxDeclNGen_1725_);
lean_inc(v_ngen_1724_);
lean_inc(v_nextMacroScope_1723_);
lean_inc(v_env_1722_);
lean_dec(v___x_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
uint64_t v_tid_1734_; lean_object* v_traces_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1748_; 
v_tid_1734_ = lean_ctor_get_uint64(v_traceState_1721_, sizeof(void*)*1);
v_traces_1735_ = lean_ctor_get(v_traceState_1721_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_traceState_1721_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1737_ = v_traceState_1721_;
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_traces_1735_);
lean_dec(v_traceState_1721_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1748_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1682_, v_traces_1735_);
lean_dec_ref(v_traces_1735_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1739_);
lean_ctor_set_uint64(v_reuseFailAlloc_1747_, sizeof(void*)*1, v_tid_1734_);
v___x_1741_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v___x_1741_);
v___x_1743_ = v___x_1732_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_env_1722_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_nextMacroScope_1723_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_ngen_1724_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v_auxDeclNGen_1725_);
lean_ctor_set(v_reuseFailAlloc_1746_, 4, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1746_, 5, v_cache_1726_);
lean_ctor_set(v_reuseFailAlloc_1746_, 6, v_recordedDeps_1727_);
lean_ctor_set(v_reuseFailAlloc_1746_, 7, v_messages_1728_);
lean_ctor_set(v_reuseFailAlloc_1746_, 8, v_infoState_1729_);
lean_ctor_set(v_reuseFailAlloc_1746_, 9, v_snapshotTasks_1730_);
v___x_1743_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_st_ref_put(v___y_1688_, v___x_1743_);
v___x_1745_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1690_);
return v___x_1745_;
}
}
}
}
}
else
{
goto v___jp_1713_;
}
}
else
{
goto v___jp_1713_;
}
}
v___jp_1750_:
{
double v___x_1752_; double v___x_1753_; double v___x_1754_; uint8_t v___x_1755_; 
v___x_1752_ = lean_unbox_float(v_snd_1699_);
v___x_1753_ = lean_unbox_float(v_fst_1698_);
v___x_1754_ = lean_float_sub(v___x_1752_, v___x_1753_);
v___x_1755_ = lean_float_decLt(v___y_1751_, v___x_1754_);
v___y_1719_ = v___x_1755_;
goto v___jp_1718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1766_, lean_object* v_collapsed_1767_, lean_object* v_tag_1768_, lean_object* v_opts_1769_, lean_object* v_clsEnabled_1770_, lean_object* v_oldTraces_1771_, lean_object* v_msg_1772_, lean_object* v_resStartStop_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v_collapsed_boxed_1779_; uint8_t v_clsEnabled_boxed_1780_; lean_object* v_res_1781_; 
v_collapsed_boxed_1779_ = lean_unbox(v_collapsed_1767_);
v_clsEnabled_boxed_1780_ = lean_unbox(v_clsEnabled_1770_);
v_res_1781_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1766_, v_collapsed_boxed_1779_, v_tag_1768_, v_opts_1769_, v_clsEnabled_boxed_1780_, v_oldTraces_1771_, v_msg_1772_, v_resStartStop_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_opts_1769_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1782_, lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_a_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_nat_dec_lt(v_a_1786_, v_upperBound_1782_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; 
lean_dec(v_a_1786_);
lean_dec(v___x_1785_);
lean_dec(v___x_1784_);
lean_dec(v___x_1783_);
v___x_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1794_, 0, v_b_1787_);
return v___x_1794_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_unsigned_to_nat(1u);
v___x_1797_ = lean_nat_add(v_a_1786_, v___x_1796_);
lean_dec(v_a_1786_);
lean_inc_n(v___x_1797_, 2);
lean_inc(v___x_1783_);
v___x_1798_ = lean_name_append_index_after(v___x_1783_, v___x_1797_);
lean_inc(v___x_1784_);
v___x_1799_ = lean_name_append_index_after(v___x_1784_, v___x_1797_);
lean_inc(v___x_1785_);
v___x_1800_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1798_, v___x_1785_, v___x_1799_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_dec_ref_known(v___x_1800_, 1);
v_a_1786_ = v___x_1797_;
v_b_1787_ = v___x_1795_;
goto _start;
}
else
{
lean_dec(v___x_1797_);
lean_dec(v___x_1785_);
lean_dec(v___x_1784_);
lean_dec(v___x_1783_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1802_, lean_object* v___x_1803_, lean_object* v___x_1804_, lean_object* v___x_1805_, lean_object* v_a_1806_, lean_object* v_b_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v_a_1806_, v_b_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v_upperBound_1802_);
return v_res_1813_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1824_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1825_ = l_Lean_Name_append(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1826_; double v___x_1827_; 
v___x_1826_ = lean_unsigned_to_nat(1000000000u);
v___x_1827_ = lean_float_of_nat(v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_toCold_1834_; lean_object* v_options_1835_; lean_object* v_inheritedTraceOptions_1836_; uint8_t v_hasTrace_1837_; lean_object* v___x_1838_; 
v_toCold_1834_ = lean_ctor_get(v_a_1831_, 0);
v_options_1835_ = lean_ctor_get(v_toCold_1834_, 2);
v_inheritedTraceOptions_1836_ = lean_ctor_get(v_toCold_1834_, 11);
v_hasTrace_1837_ = lean_ctor_get_uint8(v_options_1835_, sizeof(void*)*1);
v___x_1838_ = lean_box(0);
if (v_hasTrace_1837_ == 0)
{
lean_object* v___x_1839_; 
lean_inc(v_indName_1828_);
v___x_1839_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1903_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1903_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1903_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
if (lean_obj_tag(v_a_1840_) == 5)
{
lean_object* v_val_1844_; uint8_t v_isRec_1845_; 
v_val_1844_ = lean_ctor_get(v_a_1840_, 0);
lean_inc_ref(v_val_1844_);
lean_dec_ref_known(v_a_1840_, 1);
v_isRec_1845_ = lean_ctor_get_uint8(v_val_1844_, sizeof(void*)*6);
if (v_isRec_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1848_; 
lean_dec_ref(v_val_1844_);
lean_dec(v_indName_1828_);
v___x_1846_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1846_);
v___x_1848_ = v___x_1842_;
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
lean_object* v_toConstantVal_1850_; lean_object* v_numParams_1851_; lean_object* v_all_1852_; lean_object* v_numNested_1853_; lean_object* v_type_1854_; lean_object* v___x_1855_; 
lean_del_object(v___x_1842_);
v_toConstantVal_1850_ = lean_ctor_get(v_val_1844_, 0);
lean_inc_ref(v_toConstantVal_1850_);
v_numParams_1851_ = lean_ctor_get(v_val_1844_, 1);
lean_inc(v_numParams_1851_);
v_all_1852_ = lean_ctor_get(v_val_1844_, 3);
lean_inc(v_all_1852_);
v_numNested_1853_ = lean_ctor_get(v_val_1844_, 5);
lean_inc(v_numNested_1853_);
lean_dec_ref(v_val_1844_);
v_type_1854_ = lean_ctor_get(v_toConstantVal_1850_, 2);
lean_inc_ref(v_type_1854_);
lean_dec_ref(v_toConstantVal_1850_);
v___x_1855_ = l_Lean_Meta_isPropFormerType(v_type_1854_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1890_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1890_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1890_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_unbox(v_a_1856_);
lean_dec(v_a_1856_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_del_object(v___x_1858_);
lean_inc_n(v_indName_1828_, 2);
v___x_1861_ = l_Lean_mkRecName(v_indName_1828_);
v___x_1862_ = l_Lean_mkBelowName(v_indName_1828_);
lean_inc(v___x_1862_);
lean_inc(v_numParams_1851_);
lean_inc(v___x_1861_);
v___x_1863_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1861_, v_numParams_1851_, v___x_1862_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1884_; 
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; 
v_unused_1885_ = lean_ctor_get(v___x_1863_, 0);
lean_dec(v_unused_1885_);
v___x_1865_ = v___x_1863_;
v_isShared_1866_ = v_isSharedCheck_1884_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v___x_1863_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1884_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = l_List_get_x21Internal___redArg(v___x_1838_, v_all_1852_, v___x_1867_);
lean_dec(v_all_1852_);
v___x_1869_ = lean_name_eq(v___x_1868_, v_indName_1828_);
lean_dec(v_indName_1828_);
lean_dec(v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v___x_1862_);
lean_dec(v___x_1861_);
lean_dec(v_numNested_1853_);
lean_dec(v_numParams_1851_);
v___x_1870_ = lean_box(0);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1870_);
v___x_1872_ = v___x_1865_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_del_object(v___x_1865_);
v___x_1874_ = lean_box(0);
v___x_1875_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1853_, v___x_1861_, v___x_1862_, v_numParams_1851_, v___x_1867_, v___x_1874_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_numNested_1853_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; 
v_unused_1883_ = lean_ctor_get(v___x_1875_, 0);
lean_dec(v_unused_1883_);
v___x_1877_ = v___x_1875_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_dec(v___x_1875_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1874_);
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1874_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
return v___x_1875_;
}
}
}
}
else
{
lean_dec(v___x_1862_);
lean_dec(v___x_1861_);
lean_dec(v_numNested_1853_);
lean_dec(v_all_1852_);
lean_dec(v_numParams_1851_);
lean_dec(v_indName_1828_);
return v___x_1863_;
}
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec(v_numNested_1853_);
lean_dec(v_all_1852_);
lean_dec(v_numParams_1851_);
lean_dec(v_indName_1828_);
v___x_1886_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1886_);
v___x_1888_ = v___x_1858_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_numNested_1853_);
lean_dec(v_all_1852_);
lean_dec(v_numParams_1851_);
lean_dec(v_indName_1828_);
v_a_1891_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1855_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1855_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v_a_1840_);
lean_dec(v_indName_1828_);
v___x_1899_ = lean_box(0);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1899_);
v___x_1901_ = v___x_1842_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_indName_1828_);
v_a_1904_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1839_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1839_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
else
{
lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_a_1920_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v_a_1935_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v_a_1940_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_a_1945_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v_a_1957_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v_a_1962_; 
lean_inc(v_indName_1828_);
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1912_, 0, v_indName_1828_);
v___x_1913_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1914_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1915_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1836_, v_options_1835_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_trace_profiler;
v___x_2028_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1835_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_dec_ref(v___f_1912_);
lean_inc(v_indName_1828_);
v___x_2029_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2093_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2093_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2093_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
if (lean_obj_tag(v_a_2030_) == 5)
{
lean_object* v_val_2034_; uint8_t v_isRec_2035_; 
v_val_2034_ = lean_ctor_get(v_a_2030_, 0);
lean_inc_ref(v_val_2034_);
lean_dec_ref_known(v_a_2030_, 1);
v_isRec_2035_ = lean_ctor_get_uint8(v_val_2034_, sizeof(void*)*6);
if (v_isRec_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
lean_dec_ref(v_val_2034_);
lean_dec(v_indName_1828_);
v___x_2036_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2036_);
v___x_2038_ = v___x_2032_;
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
lean_object* v_toConstantVal_2040_; lean_object* v_numParams_2041_; lean_object* v_all_2042_; lean_object* v_numNested_2043_; lean_object* v_type_2044_; lean_object* v___x_2045_; 
lean_del_object(v___x_2032_);
v_toConstantVal_2040_ = lean_ctor_get(v_val_2034_, 0);
lean_inc_ref(v_toConstantVal_2040_);
v_numParams_2041_ = lean_ctor_get(v_val_2034_, 1);
lean_inc(v_numParams_2041_);
v_all_2042_ = lean_ctor_get(v_val_2034_, 3);
lean_inc(v_all_2042_);
v_numNested_2043_ = lean_ctor_get(v_val_2034_, 5);
lean_inc(v_numNested_2043_);
lean_dec_ref(v_val_2034_);
v_type_2044_ = lean_ctor_get(v_toConstantVal_2040_, 2);
lean_inc_ref(v_type_2044_);
lean_dec_ref(v_toConstantVal_2040_);
v___x_2045_ = l_Lean_Meta_isPropFormerType(v_type_2044_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2080_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2080_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2080_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_unbox(v_a_2046_);
lean_dec(v_a_2046_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_del_object(v___x_2048_);
lean_inc_n(v_indName_1828_, 2);
v___x_2051_ = l_Lean_mkRecName(v_indName_1828_);
v___x_2052_ = l_Lean_mkBelowName(v_indName_1828_);
lean_inc(v___x_2052_);
lean_inc(v_numParams_2041_);
lean_inc(v___x_2051_);
v___x_2053_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2051_, v_numParams_2041_, v___x_2052_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2053_, 0);
lean_dec(v_unused_2075_);
v___x_2055_ = v___x_2053_;
v_isShared_2056_ = v_isSharedCheck_2074_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v___x_2053_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2074_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = l_List_get_x21Internal___redArg(v___x_1838_, v_all_2042_, v___x_2057_);
lean_dec(v_all_2042_);
v___x_2059_ = lean_name_eq(v___x_2058_, v_indName_1828_);
lean_dec(v_indName_1828_);
lean_dec(v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
lean_dec(v___x_2052_);
lean_dec(v___x_2051_);
lean_dec(v_numNested_2043_);
lean_dec(v_numParams_2041_);
v___x_2060_ = lean_box(0);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2060_);
v___x_2062_ = v___x_2055_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_del_object(v___x_2055_);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2043_, v___x_2051_, v___x_2052_, v_numParams_2041_, v___x_2057_, v___x_2064_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_numNested_2043_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2073_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2064_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
return v___x_2065_;
}
}
}
}
else
{
lean_dec(v___x_2052_);
lean_dec(v___x_2051_);
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1828_);
return v___x_2053_;
}
}
else
{
lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1828_);
v___x_2076_ = lean_box(0);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2076_);
v___x_2078_ = v___x_2048_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
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
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1828_);
v_a_2081_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2045_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2045_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
lean_dec(v_a_2030_);
lean_dec(v_indName_1828_);
v___x_2089_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2089_);
v___x_2091_ = v___x_2032_;
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
lean_dec(v_indName_1828_);
v_a_2094_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2029_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2029_);
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
else
{
goto v___jp_1964_;
}
}
else
{
goto v___jp_1964_;
}
v___jp_1917_:
{
lean_object* v___x_1921_; double v___x_1922_; double v___x_1923_; double v___x_1924_; double v___x_1925_; double v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1921_ = lean_io_mono_nanos_now();
v___x_1922_ = lean_float_of_nat(v___y_1918_);
v___x_1923_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1924_ = lean_float_div(v___x_1922_, v___x_1923_);
v___x_1925_ = lean_float_of_nat(v___x_1921_);
v___x_1926_ = lean_float_div(v___x_1925_, v___x_1923_);
v___x_1927_ = lean_box_float(v___x_1924_);
v___x_1928_ = lean_box_float(v___x_1926_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1920_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1913_, v_hasTrace_1837_, v___x_1914_, v_options_1835_, v___x_1916_, v___y_1919_, v___f_1912_, v___x_1930_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1931_;
}
v___jp_1932_:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1935_);
v___y_1918_ = v___y_1933_;
v___y_1919_ = v___y_1934_;
v_a_1920_ = v___x_1936_;
goto v___jp_1917_;
}
v___jp_1937_:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_a_1940_);
v___y_1918_ = v___y_1938_;
v___y_1919_ = v___y_1939_;
v_a_1920_ = v___x_1941_;
goto v___jp_1917_;
}
v___jp_1942_:
{
lean_object* v___x_1946_; double v___x_1947_; double v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1946_ = lean_io_get_num_heartbeats();
v___x_1947_ = lean_float_of_nat(v___y_1943_);
v___x_1948_ = lean_float_of_nat(v___x_1946_);
v___x_1949_ = lean_box_float(v___x_1947_);
v___x_1950_ = lean_box_float(v___x_1948_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_a_1945_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1913_, v_hasTrace_1837_, v___x_1914_, v_options_1835_, v___x_1916_, v___y_1944_, v___f_1912_, v___x_1952_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
return v___x_1953_;
}
v___jp_1954_:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1957_);
v___y_1943_ = v___y_1955_;
v___y_1944_ = v___y_1956_;
v_a_1945_ = v___x_1958_;
goto v___jp_1942_;
}
v___jp_1959_:
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_a_1962_);
v___y_1943_ = v___y_1960_;
v___y_1944_ = v___y_1961_;
v_a_1945_ = v___x_1963_;
goto v___jp_1942_;
}
v___jp_1964_:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1965_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1832_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1968_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1835_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1828_);
v___x_1970_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref_known(v___x_1970_, 1);
if (lean_obj_tag(v_a_1971_) == 5)
{
lean_object* v_val_1972_; uint8_t v_isRec_1973_; 
v_val_1972_ = lean_ctor_get(v_a_1971_, 0);
lean_inc_ref(v_val_1972_);
lean_dec_ref_known(v_a_1971_, 1);
v_isRec_1973_ = lean_ctor_get_uint8(v_val_1972_, sizeof(void*)*6);
if (v_isRec_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref(v_val_1972_);
lean_dec(v_indName_1828_);
v___x_1974_ = lean_box(0);
v___y_1933_ = v___x_1969_;
v___y_1934_ = v_a_1966_;
v_a_1935_ = v___x_1974_;
goto v___jp_1932_;
}
else
{
lean_object* v_toConstantVal_1975_; lean_object* v_numParams_1976_; lean_object* v_all_1977_; lean_object* v_numNested_1978_; lean_object* v_type_1979_; lean_object* v___x_1980_; 
v_toConstantVal_1975_ = lean_ctor_get(v_val_1972_, 0);
lean_inc_ref(v_toConstantVal_1975_);
v_numParams_1976_ = lean_ctor_get(v_val_1972_, 1);
lean_inc(v_numParams_1976_);
v_all_1977_ = lean_ctor_get(v_val_1972_, 3);
lean_inc(v_all_1977_);
v_numNested_1978_ = lean_ctor_get(v_val_1972_, 5);
lean_inc(v_numNested_1978_);
lean_dec_ref(v_val_1972_);
v_type_1979_ = lean_ctor_get(v_toConstantVal_1975_, 2);
lean_inc_ref(v_type_1979_);
lean_dec_ref(v_toConstantVal_1975_);
v___x_1980_ = l_Lean_Meta_isPropFormerType(v_type_1979_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; uint8_t v___x_1982_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = lean_unbox(v_a_1981_);
lean_dec(v_a_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_inc_n(v_indName_1828_, 2);
v___x_1983_ = l_Lean_mkRecName(v_indName_1828_);
v___x_1984_ = l_Lean_mkBelowName(v_indName_1828_);
lean_inc(v___x_1984_);
lean_inc(v_numParams_1976_);
lean_inc(v___x_1983_);
v___x_1985_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1983_, v_numParams_1976_, v___x_1984_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
lean_dec_ref_known(v___x_1985_, 1);
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = l_List_get_x21Internal___redArg(v___x_1838_, v_all_1977_, v___x_1986_);
lean_dec(v_all_1977_);
v___x_1988_ = lean_name_eq(v___x_1987_, v_indName_1828_);
lean_dec(v_indName_1828_);
lean_dec(v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
lean_dec(v_numNested_1978_);
lean_dec(v_numParams_1976_);
v___x_1989_ = lean_box(0);
v___y_1933_ = v___x_1969_;
v___y_1934_ = v_a_1966_;
v_a_1935_ = v___x_1989_;
goto v___jp_1932_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = lean_box(0);
v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1978_, v___x_1983_, v___x_1984_, v_numParams_1976_, v___x_1986_, v___x_1990_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_numNested_1978_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_dec_ref_known(v___x_1991_, 1);
v___y_1933_ = v___x_1969_;
v___y_1934_ = v_a_1966_;
v_a_1935_ = v___x_1990_;
goto v___jp_1932_;
}
else
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1938_ = v___x_1969_;
v___y_1939_ = v_a_1966_;
v_a_1940_ = v_a_1992_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v_a_1993_; 
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
lean_dec(v_numNested_1978_);
lean_dec(v_all_1977_);
lean_dec(v_numParams_1976_);
lean_dec(v_indName_1828_);
v_a_1993_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1985_, 1);
v___y_1938_ = v___x_1969_;
v___y_1939_ = v_a_1966_;
v_a_1940_ = v_a_1993_;
goto v___jp_1937_;
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v_numNested_1978_);
lean_dec(v_all_1977_);
lean_dec(v_numParams_1976_);
lean_dec(v_indName_1828_);
v___x_1994_ = lean_box(0);
v___y_1933_ = v___x_1969_;
v___y_1934_ = v_a_1966_;
v_a_1935_ = v___x_1994_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_1995_; 
lean_dec(v_numNested_1978_);
lean_dec(v_all_1977_);
lean_dec(v_numParams_1976_);
lean_dec(v_indName_1828_);
v_a_1995_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1938_ = v___x_1969_;
v___y_1939_ = v_a_1966_;
v_a_1940_ = v_a_1995_;
goto v___jp_1937_;
}
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_a_1971_);
lean_dec(v_indName_1828_);
v___x_1996_ = lean_box(0);
v___y_1933_ = v___x_1969_;
v___y_1934_ = v_a_1966_;
v_a_1935_ = v___x_1996_;
goto v___jp_1932_;
}
}
else
{
lean_object* v_a_1997_; 
lean_dec(v_indName_1828_);
v_a_1997_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1970_, 1);
v___y_1938_ = v___x_1969_;
v___y_1939_ = v_a_1966_;
v_a_1940_ = v_a_1997_;
goto v___jp_1937_;
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1828_);
v___x_1999_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
if (lean_obj_tag(v_a_2000_) == 5)
{
lean_object* v_val_2001_; uint8_t v_isRec_2002_; 
v_val_2001_ = lean_ctor_get(v_a_2000_, 0);
lean_inc_ref(v_val_2001_);
lean_dec_ref_known(v_a_2000_, 1);
v_isRec_2002_ = lean_ctor_get_uint8(v_val_2001_, sizeof(void*)*6);
if (v_isRec_2002_ == 0)
{
lean_object* v___x_2003_; 
lean_dec_ref(v_val_2001_);
lean_dec(v_indName_1828_);
v___x_2003_ = lean_box(0);
v___y_1955_ = v___x_1998_;
v___y_1956_ = v_a_1966_;
v_a_1957_ = v___x_2003_;
goto v___jp_1954_;
}
else
{
lean_object* v_toConstantVal_2004_; lean_object* v_numParams_2005_; lean_object* v_all_2006_; lean_object* v_numNested_2007_; lean_object* v_type_2008_; lean_object* v___x_2009_; 
v_toConstantVal_2004_ = lean_ctor_get(v_val_2001_, 0);
lean_inc_ref(v_toConstantVal_2004_);
v_numParams_2005_ = lean_ctor_get(v_val_2001_, 1);
lean_inc(v_numParams_2005_);
v_all_2006_ = lean_ctor_get(v_val_2001_, 3);
lean_inc(v_all_2006_);
v_numNested_2007_ = lean_ctor_get(v_val_2001_, 5);
lean_inc(v_numNested_2007_);
lean_dec_ref(v_val_2001_);
v_type_2008_ = lean_ctor_get(v_toConstantVal_2004_, 2);
lean_inc_ref(v_type_2008_);
lean_dec_ref(v_toConstantVal_2004_);
v___x_2009_ = l_Lean_Meta_isPropFormerType(v_type_2008_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_inc_n(v_indName_1828_, 2);
v___x_2012_ = l_Lean_mkRecName(v_indName_1828_);
v___x_2013_ = l_Lean_mkBelowName(v_indName_1828_);
lean_inc(v___x_2013_);
lean_inc(v_numParams_2005_);
lean_inc(v___x_2012_);
v___x_2014_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2012_, v_numParams_2005_, v___x_2013_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
lean_dec_ref_known(v___x_2014_, 1);
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = l_List_get_x21Internal___redArg(v___x_1838_, v_all_2006_, v___x_2015_);
lean_dec(v_all_2006_);
v___x_2017_ = lean_name_eq(v___x_2016_, v_indName_1828_);
lean_dec(v_indName_1828_);
lean_dec(v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec(v___x_2013_);
lean_dec(v___x_2012_);
lean_dec(v_numNested_2007_);
lean_dec(v_numParams_2005_);
v___x_2018_ = lean_box(0);
v___y_1955_ = v___x_1998_;
v___y_1956_ = v_a_1966_;
v_a_1957_ = v___x_2018_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2007_, v___x_2012_, v___x_2013_, v_numParams_2005_, v___x_2015_, v___x_2019_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_numNested_2007_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_dec_ref_known(v___x_2020_, 1);
v___y_1955_ = v___x_1998_;
v___y_1956_ = v_a_1966_;
v_a_1957_ = v___x_2019_;
goto v___jp_1954_;
}
else
{
lean_object* v_a_2021_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___y_1960_ = v___x_1998_;
v___y_1961_ = v_a_1966_;
v_a_1962_ = v_a_2021_;
goto v___jp_1959_;
}
}
}
else
{
lean_object* v_a_2022_; 
lean_dec(v___x_2013_);
lean_dec(v___x_2012_);
lean_dec(v_numNested_2007_);
lean_dec(v_all_2006_);
lean_dec(v_numParams_2005_);
lean_dec(v_indName_1828_);
v_a_2022_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1960_ = v___x_1998_;
v___y_1961_ = v_a_1966_;
v_a_1962_ = v_a_2022_;
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2023_; 
lean_dec(v_numNested_2007_);
lean_dec(v_all_2006_);
lean_dec(v_numParams_2005_);
lean_dec(v_indName_1828_);
v___x_2023_ = lean_box(0);
v___y_1955_ = v___x_1998_;
v___y_1956_ = v_a_1966_;
v_a_1957_ = v___x_2023_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2024_; 
lean_dec(v_numNested_2007_);
lean_dec(v_all_2006_);
lean_dec(v_numParams_2005_);
lean_dec(v_indName_1828_);
v_a_2024_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2009_, 1);
v___y_1960_ = v___x_1998_;
v___y_1961_ = v_a_1966_;
v_a_1962_ = v_a_2024_;
goto v___jp_1959_;
}
}
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_a_2000_);
lean_dec(v_indName_1828_);
v___x_2025_ = lean_box(0);
v___y_1955_ = v___x_1998_;
v___y_1956_ = v_a_1966_;
v_a_1957_ = v___x_2025_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2026_; 
lean_dec(v_indName_1828_);
v_a_2026_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1960_ = v___x_1998_;
v___y_1961_ = v_a_1966_;
v_a_1962_ = v_a_2026_;
goto v___jp_1959_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_mkBelow(v_indName_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2109_, lean_object* v___x_2110_, lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_inst_2113_, lean_object* v_R_2114_, lean_object* v_a_2115_, lean_object* v_b_2116_, lean_object* v_c_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2109_, v___x_2110_, v___x_2111_, v___x_2112_, v_a_2115_, v_b_2116_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2124_, lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_inst_2128_, lean_object* v_R_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v_c_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2124_, v___x_2125_, v___x_2126_, v___x_2127_, v_inst_2128_, v_R_2129_, v_a_2130_, v_b_2131_, v_c_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v_upperBound_2124_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2139_, lean_object* v_x_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2140_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2147_, v_x_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
if (lean_obj_tag(v_a_2155_) == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = l_List_reverse___redArg(v_a_2156_);
return v___x_2157_;
}
else
{
lean_object* v_head_2158_; lean_object* v_tail_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2168_; 
v_head_2158_ = lean_ctor_get(v_a_2155_, 0);
v_tail_2159_ = lean_ctor_get(v_a_2155_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2161_ = v_a_2155_;
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_tail_2159_);
lean_inc(v_head_2158_);
lean_dec(v_a_2155_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2168_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2163_; lean_object* v___x_2165_; 
v___x_2163_ = l_Lean_MessageData_ofExpr(v_head_2158_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 1, v_a_2156_);
lean_ctor_set(v___x_2161_, 0, v___x_2163_);
v___x_2165_ = v___x_2161_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_a_2156_);
v___x_2165_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
v_a_2155_ = v_tail_2159_;
v_a_2156_ = v___x_2165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2169_, lean_object* v_v_2170_, lean_object* v_i_2171_){
_start:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_array_get_size(v_xs_2169_);
v___x_2173_ = lean_nat_dec_lt(v_i_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v_i_2171_);
v___x_2174_ = lean_box(0);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2175_ = lean_array_fget_borrowed(v_xs_2169_, v_i_2171_);
v___x_2176_ = lean_expr_eqv(v___x_2175_, v_v_2170_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_add(v_i_2171_, v___x_2177_);
lean_dec(v_i_2171_);
v_i_2171_ = v___x_2178_;
goto _start;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_i_2171_);
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2181_, lean_object* v_v_2182_, lean_object* v_i_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2181_, v_v_2182_, v_i_2183_);
lean_dec_ref(v_v_2182_);
lean_dec_ref(v_xs_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2185_, lean_object* v_v_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2185_, v_v_2186_, v___x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2189_, lean_object* v_v_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2189_, v_v_2190_);
lean_dec_ref(v_v_2190_);
lean_dec_ref(v_xs_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2192_, lean_object* v_v_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2192_, v_v_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_box(0);
return v___x_2195_;
}
else
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
v_val_2196_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2194_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v___x_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_val_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2204_, lean_object* v_v_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2204_, v_v_2205_);
lean_dec_ref(v_v_2205_);
lean_dec_ref(v_xs_2204_);
return v_res_2206_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2213_, lean_object* v_prods_2214_, lean_object* v_motives_2215_, lean_object* v_fs_2216_, lean_object* v_minor__type_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v_x_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
if (lean_obj_tag(v_x_2218_) == 5)
{
lean_object* v_fn_2226_; lean_object* v_arg_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_fn_2226_ = lean_ctor_get(v_x_2218_, 0);
lean_inc_ref(v_fn_2226_);
v_arg_2227_ = lean_ctor_get(v_x_2218_, 1);
lean_inc_ref(v_arg_2227_);
lean_dec_ref_known(v_x_2218_, 2);
v___x_2228_ = lean_array_set(v_x_2219_, v_x_2220_, v_arg_2227_);
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_sub(v_x_2220_, v___x_2229_);
lean_dec(v_x_2220_);
v_x_2218_ = v_fn_2226_;
v_x_2219_ = v___x_2228_;
v_x_2220_ = v___x_2230_;
goto _start;
}
else
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v_x_2220_);
v___x_2232_ = l_Lean_instInhabitedExpr;
v___x_2233_ = l_Lean_Meta_PProdN_mk(v_rlvl_2213_, v_prods_2214_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2215_, v_x_2218_);
lean_dec_ref(v_x_2218_);
if (lean_obj_tag(v___x_2235_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec_ref(v_minor__type_2217_);
lean_dec_ref(v_motives_2215_);
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = lean_array_get_borrowed(v___x_2232_, v_fs_2216_, v_val_2236_);
lean_dec(v_val_2236_);
lean_inc(v_a_2234_);
v___x_2238_ = lean_array_push(v_x_2219_, v_a_2234_);
lean_inc(v___x_2237_);
v___x_2239_ = l_Lean_mkAppN(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = l_Lean_Meta_mkPProdMk(v___x_2239_, v_a_2234_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec(v___x_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_x_2219_);
v___x_2241_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2242_ = l_Lean_MessageData_ofExpr(v_minor__type_2217_);
v___x_2243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2241_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2243_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = lean_array_to_list(v_motives_2215_);
v___x_2247_ = lean_box(0);
v___x_2248_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2246_, v___x_2247_);
v___x_2249_ = l_Lean_MessageData_ofList(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2245_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2250_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2251_;
}
}
else
{
lean_dec_ref(v_x_2219_);
lean_dec_ref(v_x_2218_);
lean_dec_ref(v_minor__type_2217_);
lean_dec_ref(v_motives_2215_);
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2252_, lean_object* v_prods_2253_, lean_object* v_motives_2254_, lean_object* v_fs_2255_, lean_object* v_minor__type_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_, lean_object* v_x_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2252_, v_prods_2253_, v_motives_2254_, v_fs_2255_, v_minor__type_2256_, v_x_2257_, v_x_2258_, v_x_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_fs_2255_);
return v_res_2265_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2266_; lean_object* v_dummy_2267_; 
v___x_2266_ = lean_box(0);
v_dummy_2267_ = l_Lean_Expr_sort___override(v___x_2266_);
return v_dummy_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2268_, lean_object* v_head_2269_, lean_object* v_belows_2270_, lean_object* v_prods_2271_, lean_object* v_rlvl_2272_, lean_object* v_fs_2273_, lean_object* v_minor__type_2274_, lean_object* v_tail_2275_, lean_object* v_arg__args_2276_, lean_object* v_arg__type_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2268_, v_head_2269_, v_belows_2270_, v_prods_2271_, v_rlvl_2272_, v_fs_2273_, v_minor__type_2274_, v_tail_2275_, v_arg__args_2276_, v_arg__type_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_arg__args_2276_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2284_, lean_object* v_motives_2285_, lean_object* v_belows_2286_, lean_object* v_fs_2287_, lean_object* v_minor__type_2288_, lean_object* v_prods_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
if (lean_obj_tag(v_a_2290_) == 0)
{
lean_object* v_dummy_2296_; lean_object* v_nargs_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_belows_2286_);
v_dummy_2296_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2297_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2288_);
lean_inc(v_nargs_2297_);
v___x_2298_ = lean_mk_array(v_nargs_2297_, v_dummy_2296_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_nat_sub(v_nargs_2297_, v___x_2299_);
lean_dec(v_nargs_2297_);
lean_inc_ref(v_minor__type_2288_);
v___x_2301_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2284_, v_prods_2289_, v_motives_2285_, v_fs_2287_, v_minor__type_2288_, v_minor__type_2288_, v___x_2298_, v___x_2300_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec_ref(v_fs_2287_);
return v___x_2301_;
}
else
{
lean_object* v_head_2302_; lean_object* v_tail_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; 
v_head_2302_ = lean_ctor_get(v_a_2290_, 0);
lean_inc_n(v_head_2302_, 2);
v_tail_2303_ = lean_ctor_get(v_a_2290_, 1);
lean_inc(v_tail_2303_);
lean_dec_ref_known(v_a_2290_, 2);
v___f_2304_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2304_, 0, v_motives_2285_);
lean_closure_set(v___f_2304_, 1, v_head_2302_);
lean_closure_set(v___f_2304_, 2, v_belows_2286_);
lean_closure_set(v___f_2304_, 3, v_prods_2289_);
lean_closure_set(v___f_2304_, 4, v_rlvl_2284_);
lean_closure_set(v___f_2304_, 5, v_fs_2287_);
lean_closure_set(v___f_2304_, 6, v_minor__type_2288_);
lean_closure_set(v___f_2304_, 7, v_tail_2303_);
lean_inc(v_a_2294_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2292_);
lean_inc_ref(v_a_2291_);
v___x_2305_ = lean_infer_type(v_head_2302_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; uint8_t v___x_2307_; lean_object* v___x_2308_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = 0;
v___x_2308_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2306_, v___f_2304_, v___x_2307_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
return v___x_2308_;
}
else
{
lean_dec_ref(v___f_2304_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2309_, lean_object* v_rlvl_2310_, lean_object* v_motives_2311_, lean_object* v_belows_2312_, lean_object* v_fs_2313_, lean_object* v_minor__type_2314_, lean_object* v_tail_2315_, uint8_t v___x_2316_, uint8_t v___x_2317_, uint8_t v___x_2318_, lean_object* v_arg_x27_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_inc_ref(v_arg_x27_2319_);
v___x_2325_ = lean_array_push(v_prods_2309_, v_arg_x27_2319_);
v___x_2326_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2310_, v_motives_2311_, v_belows_2312_, v_fs_2313_, v_minor__type_2314_, v___x_2325_, v_tail_2315_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2328_);
v___x_2330_ = lean_array_push(v___x_2329_, v_arg_x27_2319_);
v___x_2331_ = l_Lean_Meta_mkLambdaFVars(v___x_2330_, v_a_2327_, v___x_2316_, v___x_2317_, v___x_2316_, v___x_2317_, v___x_2318_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec_ref(v___x_2330_);
return v___x_2331_;
}
else
{
lean_dec_ref(v_arg_x27_2319_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2332_, lean_object* v_rlvl_2333_, lean_object* v_motives_2334_, lean_object* v_belows_2335_, lean_object* v_fs_2336_, lean_object* v_minor__type_2337_, lean_object* v_tail_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v___x_2341_, lean_object* v_arg_x27_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
uint8_t v___x_1689__boxed_2348_; uint8_t v___x_1690__boxed_2349_; uint8_t v___x_1691__boxed_2350_; lean_object* v_res_2351_; 
v___x_1689__boxed_2348_ = lean_unbox(v___x_2339_);
v___x_1690__boxed_2349_ = lean_unbox(v___x_2340_);
v___x_1691__boxed_2350_ = lean_unbox(v___x_2341_);
v_res_2351_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2332_, v_rlvl_2333_, v_motives_2334_, v_belows_2335_, v_fs_2336_, v_minor__type_2337_, v_tail_2338_, v___x_1689__boxed_2348_, v___x_1690__boxed_2349_, v___x_1691__boxed_2350_, v_arg_x27_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2352_, lean_object* v_head_2353_, lean_object* v_belows_2354_, lean_object* v_arg__type_2355_, lean_object* v_prods_2356_, lean_object* v_rlvl_2357_, lean_object* v_fs_2358_, lean_object* v_minor__type_2359_, lean_object* v_tail_2360_, lean_object* v_arg__args_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 5)
{
lean_object* v_fn_2370_; lean_object* v_arg_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v_fn_2370_ = lean_ctor_get(v_x_2362_, 0);
lean_inc_ref(v_fn_2370_);
v_arg_2371_ = lean_ctor_get(v_x_2362_, 1);
lean_inc_ref(v_arg_2371_);
lean_dec_ref_known(v_x_2362_, 2);
v___x_2372_ = lean_array_set(v_x_2363_, v_x_2364_, v_arg_2371_);
v___x_2373_ = lean_unsigned_to_nat(1u);
v___x_2374_ = lean_nat_sub(v_x_2364_, v___x_2373_);
lean_dec(v_x_2364_);
v_x_2362_ = v_fn_2370_;
v_x_2363_ = v___x_2372_;
v_x_2364_ = v___x_2374_;
goto _start;
}
else
{
lean_object* v___x_2376_; 
lean_dec(v_x_2364_);
v___x_2376_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2352_, v_x_2362_);
lean_dec_ref(v_x_2362_);
if (lean_obj_tag(v___x_2376_) == 1)
{
lean_object* v_val_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_val_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_val_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v___x_2378_ = l_Lean_instInhabitedExpr;
v___x_2379_ = l_Lean_Expr_fvarId_x21(v_head_2353_);
lean_dec_ref(v_head_2353_);
v___x_2380_ = l_Lean_FVarId_getUserName___redArg(v___x_2379_, v___y_2365_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = lean_array_get_borrowed(v___x_2378_, v_belows_2354_, v_val_2377_);
lean_dec(v_val_2377_);
lean_inc(v___x_2382_);
v___x_2383_ = l_Lean_mkAppN(v___x_2382_, v_x_2363_);
lean_dec_ref(v_x_2363_);
v___x_2384_ = l_Lean_Meta_mkPProd(v_arg__type_2355_, v___x_2383_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___f_2392_; lean_object* v___x_2393_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
v___x_2386_ = 0;
v___x_2387_ = 1;
v___x_2388_ = 1;
v___x_2389_ = lean_box(v___x_2386_);
v___x_2390_ = lean_box(v___x_2387_);
v___x_2391_ = lean_box(v___x_2388_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2392_, 0, v_prods_2356_);
lean_closure_set(v___f_2392_, 1, v_rlvl_2357_);
lean_closure_set(v___f_2392_, 2, v_motives_2352_);
lean_closure_set(v___f_2392_, 3, v_belows_2354_);
lean_closure_set(v___f_2392_, 4, v_fs_2358_);
lean_closure_set(v___f_2392_, 5, v_minor__type_2359_);
lean_closure_set(v___f_2392_, 6, v_tail_2360_);
lean_closure_set(v___f_2392_, 7, v___x_2389_);
lean_closure_set(v___f_2392_, 8, v___x_2390_);
lean_closure_set(v___f_2392_, 9, v___x_2391_);
v___x_2393_ = l_Lean_Meta_mkForallFVars(v_arg__args_2361_, v_a_2385_, v___x_2386_, v___x_2387_, v___x_2387_, v___x_2388_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2381_, v_a_2394_, v___f_2392_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
return v___x_2395_;
}
else
{
lean_dec_ref(v___f_2392_);
lean_dec(v_a_2381_);
return v___x_2393_;
}
}
else
{
lean_dec(v_a_2381_);
lean_dec(v_tail_2360_);
lean_dec_ref(v_minor__type_2359_);
lean_dec_ref(v_fs_2358_);
lean_dec(v_rlvl_2357_);
lean_dec_ref(v_prods_2356_);
lean_dec_ref(v_belows_2354_);
lean_dec_ref(v_motives_2352_);
return v___x_2384_;
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_val_2377_);
lean_dec_ref(v_x_2363_);
lean_dec(v_tail_2360_);
lean_dec_ref(v_minor__type_2359_);
lean_dec_ref(v_fs_2358_);
lean_dec(v_rlvl_2357_);
lean_dec_ref(v_prods_2356_);
lean_dec_ref(v_arg__type_2355_);
lean_dec_ref(v_belows_2354_);
lean_dec_ref(v_motives_2352_);
v_a_2396_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2380_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2380_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v___x_2404_; 
lean_dec(v___x_2376_);
lean_dec_ref(v_x_2363_);
lean_dec_ref(v_arg__type_2355_);
v___x_2404_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2357_, v_motives_2352_, v_belows_2354_, v_fs_2358_, v_minor__type_2359_, v_prods_2356_, v_tail_2360_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2412_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_mk_empty_array_with_capacity(v___x_2406_);
v___x_2408_ = lean_array_push(v___x_2407_, v_head_2353_);
v___x_2409_ = 0;
v___x_2410_ = 1;
v___x_2411_ = 1;
v___x_2412_ = l_Lean_Meta_mkLambdaFVars(v___x_2408_, v_a_2405_, v___x_2409_, v___x_2410_, v___x_2409_, v___x_2410_, v___x_2411_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref(v___x_2408_);
return v___x_2412_;
}
else
{
lean_dec_ref(v_head_2353_);
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2413_, lean_object* v_head_2414_, lean_object* v_belows_2415_, lean_object* v_prods_2416_, lean_object* v_rlvl_2417_, lean_object* v_fs_2418_, lean_object* v_minor__type_2419_, lean_object* v_tail_2420_, lean_object* v_arg__args_2421_, lean_object* v_arg__type_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_dummy_2428_; lean_object* v_nargs_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v_dummy_2428_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2429_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2422_);
lean_inc(v_nargs_2429_);
v___x_2430_ = lean_mk_array(v_nargs_2429_, v_dummy_2428_);
v___x_2431_ = lean_unsigned_to_nat(1u);
v___x_2432_ = lean_nat_sub(v_nargs_2429_, v___x_2431_);
lean_dec(v_nargs_2429_);
lean_inc_ref(v_arg__type_2422_);
v___x_2433_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2413_, v_head_2414_, v_belows_2415_, v_arg__type_2422_, v_prods_2416_, v_rlvl_2417_, v_fs_2418_, v_minor__type_2419_, v_tail_2420_, v_arg__args_2421_, v_arg__type_2422_, v___x_2430_, v___x_2432_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2434_, lean_object* v_motives_2435_, lean_object* v_belows_2436_, lean_object* v_fs_2437_, lean_object* v_minor__type_2438_, lean_object* v_prods_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2434_, v_motives_2435_, v_belows_2436_, v_fs_2437_, v_minor__type_2438_, v_prods_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2447_ = _args[0];
lean_object* v_head_2448_ = _args[1];
lean_object* v_belows_2449_ = _args[2];
lean_object* v_arg__type_2450_ = _args[3];
lean_object* v_prods_2451_ = _args[4];
lean_object* v_rlvl_2452_ = _args[5];
lean_object* v_fs_2453_ = _args[6];
lean_object* v_minor__type_2454_ = _args[7];
lean_object* v_tail_2455_ = _args[8];
lean_object* v_arg__args_2456_ = _args[9];
lean_object* v_x_2457_ = _args[10];
lean_object* v_x_2458_ = _args[11];
lean_object* v_x_2459_ = _args[12];
lean_object* v___y_2460_ = _args[13];
lean_object* v___y_2461_ = _args[14];
lean_object* v___y_2462_ = _args[15];
lean_object* v___y_2463_ = _args[16];
lean_object* v___y_2464_ = _args[17];
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2447_, v_head_2448_, v_belows_2449_, v_arg__type_2450_, v_prods_2451_, v_rlvl_2452_, v_fs_2453_, v_minor__type_2454_, v_tail_2455_, v_arg__args_2456_, v_x_2457_, v_x_2458_, v_x_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v_arg__args_2456_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2466_, lean_object* v_motives_2467_, lean_object* v_belows_2468_, lean_object* v_fs_2469_, lean_object* v_minor__args_2470_, lean_object* v_minor__type_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2478_ = lean_array_to_list(v_minor__args_2470_);
v___x_2479_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2466_, v_motives_2467_, v_belows_2468_, v_fs_2469_, v_minor__type_2471_, v___x_2477_, v___x_2478_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2480_, lean_object* v_motives_2481_, lean_object* v_belows_2482_, lean_object* v_fs_2483_, lean_object* v_minor__args_2484_, lean_object* v_minor__type_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2480_, v_motives_2481_, v_belows_2482_, v_fs_2483_, v_minor__args_2484_, v_minor__type_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2492_, lean_object* v_motives_2493_, lean_object* v_belows_2494_, lean_object* v_fs_2495_, lean_object* v_minorType_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_){
_start:
{
lean_object* v___f_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; 
v___f_2502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2502_, 0, v_rlvl_2492_);
lean_closure_set(v___f_2502_, 1, v_motives_2493_);
lean_closure_set(v___f_2502_, 2, v_belows_2494_);
lean_closure_set(v___f_2502_, 3, v_fs_2495_);
v___x_2503_ = 0;
v___x_2504_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2496_, v___f_2502_, v___x_2503_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2505_, lean_object* v_motives_2506_, lean_object* v_belows_2507_, lean_object* v_fs_2508_, lean_object* v_minorType_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2505_, v_motives_2506_, v_belows_2507_, v_fs_2508_, v_minorType_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec_ref(v_a_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___f_2522_; lean_object* v___x_30018__overap_2523_; lean_object* v___x_2524_; 
v___f_2522_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_30018__overap_2523_ = lean_panic_fn_borrowed(v___f_2522_, v_msg_2516_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
v___x_2524_ = lean_apply_5(v___x_30018__overap_2523_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, lean_box(0));
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2532_, lean_object* v___y_2533_){
_start:
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_Expr_hasMVar(v_e_2532_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_e_2532_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; lean_object* v_mctx_2538_; lean_object* v___x_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; lean_object* v_cache_2543_; lean_object* v_zetaDeltaFVarIds_2544_; lean_object* v_postponed_2545_; lean_object* v_diag_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2555_; 
v___x_2537_ = lean_st_ref_get(v___y_2533_);
v_mctx_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_mctx_2538_);
lean_dec(v___x_2537_);
v___x_2539_ = l_Lean_instantiateMVarsCore(v_mctx_2538_, v_e_2532_);
v_fst_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_fst_2540_);
v_snd_2541_ = lean_ctor_get(v___x_2539_, 1);
lean_inc(v_snd_2541_);
lean_dec_ref(v___x_2539_);
v___x_2542_ = lean_st_ref_take(v___y_2533_);
v_cache_2543_ = lean_ctor_get(v___x_2542_, 1);
v_zetaDeltaFVarIds_2544_ = lean_ctor_get(v___x_2542_, 2);
v_postponed_2545_ = lean_ctor_get(v___x_2542_, 3);
v_diag_2546_ = lean_ctor_get(v___x_2542_, 4);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v___x_2542_, 0);
lean_dec(v_unused_2556_);
v___x_2548_ = v___x_2542_;
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_diag_2546_);
lean_inc(v_postponed_2545_);
lean_inc(v_zetaDeltaFVarIds_2544_);
lean_inc(v_cache_2543_);
lean_dec(v___x_2542_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_snd_2541_);
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_snd_2541_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_cache_2543_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_zetaDeltaFVarIds_2544_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_postponed_2545_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v_diag_2546_);
v___x_2551_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_st_ref_put(v___y_2533_, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_fst_2540_);
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2557_, v___y_2558_);
lean_dec(v___y_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2561_, v___y_2563_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v_env_2579_; lean_object* v_toConstantVal_2580_; lean_object* v_value_2581_; lean_object* v_all_2582_; lean_object* v_type_2589_; uint8_t v___x_2590_; 
v___x_2578_ = lean_st_ref_get(v___y_2576_);
v_env_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc_ref_n(v_env_2579_, 2);
lean_dec(v___x_2578_);
v_toConstantVal_2580_ = lean_ctor_get(v_thm_2575_, 0);
v_value_2581_ = lean_ctor_get(v_thm_2575_, 1);
v_all_2582_ = lean_ctor_get(v_thm_2575_, 2);
v_type_2589_ = lean_ctor_get(v_toConstantVal_2580_, 2);
v___x_2590_ = l_Lean_Environment_hasUnsafe(v_env_2579_, v_type_2589_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
v___x_2591_ = l_Lean_Environment_hasUnsafe(v_env_2579_, v_value_2581_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_thm_2575_);
v___x_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
return v___x_2593_;
}
else
{
lean_inc(v_all_2582_);
lean_inc_ref(v_value_2581_);
lean_inc_ref(v_toConstantVal_2580_);
lean_dec_ref(v_thm_2575_);
goto v___jp_2583_;
}
}
else
{
lean_inc(v_all_2582_);
lean_inc_ref(v_value_2581_);
lean_inc_ref(v_toConstantVal_2580_);
lean_dec_ref(v_env_2579_);
lean_dec_ref(v_thm_2575_);
goto v___jp_2583_;
}
v___jp_2583_:
{
lean_object* v___x_2584_; uint8_t v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2584_ = lean_box(0);
v___x_2585_ = 0;
v___x_2586_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2586_, 0, v_toConstantVal_2580_);
lean_ctor_set(v___x_2586_, 1, v_value_2581_);
lean_ctor_set(v___x_2586_, 2, v___x_2584_);
lean_ctor_set(v___x_2586_, 3, v_all_2582_);
lean_ctor_set_uint8(v___x_2586_, sizeof(void*)*4, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
return v___x_2588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2594_, v___y_2595_);
lean_dec(v___y_2595_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2598_, v___y_2602_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v_all_2616_, lean_object* v___x_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v___y_2622_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_array_get_size(v_all_2616_);
v___x_2627_ = lean_nat_dec_lt(v_x_2620_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2628_ = lean_array_get_borrowed(v___x_2617_, v_all_2616_, v___x_2618_);
v___x_2629_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2630_ = lean_nat_sub(v_x_2620_, v___x_2626_);
v___x_2631_ = lean_nat_add(v___x_2630_, v___x_2619_);
lean_dec(v___x_2630_);
v___x_2632_ = l_Nat_reprFast(v___x_2631_);
v___x_2633_ = lean_string_append(v___x_2629_, v___x_2632_);
lean_dec_ref(v___x_2632_);
lean_inc(v___x_2628_);
v___x_2634_ = l_Lean_Name_str___override(v___x_2628_, v___x_2633_);
v___y_2622_ = v___x_2634_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_array_fget_borrowed(v_all_2616_, v_x_2620_);
lean_inc(v___x_2635_);
v___x_2636_ = l_Lean_mkBelowName(v___x_2635_);
v___y_2622_ = v___x_2636_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = l_Lean_Expr_const___override(v___y_2622_, v___x_2613_);
v___x_2624_ = l_Array_append___redArg(v___x_2614_, v___x_2615_);
v___x_2625_ = l_Lean_mkAppN(v___x_2623_, v___x_2624_);
lean_dec_ref(v___x_2624_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2637_, lean_object* v___x_2638_, lean_object* v___x_2639_, lean_object* v_all_2640_, lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v___x_2643_, lean_object* v_x_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2637_, v___x_2638_, v___x_2639_, v_all_2640_, v___x_2641_, v___x_2642_, v___x_2643_, v_x_2644_);
lean_dec(v_x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
lean_dec(v___x_2641_);
lean_dec_ref(v_all_2640_);
lean_dec_ref(v___x_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2646_, lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v_fs_2649_, lean_object* v_as_2650_, size_t v_sz_2651_, size_t v_i_2652_, lean_object* v_b_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_2659_; 
v___x_2659_ = lean_usize_dec_lt(v_i_2652_, v_sz_2651_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref(v_fs_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v___x_2647_);
lean_dec(v___x_2646_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_b_2653_);
return v___x_2660_;
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2661_ = lean_array_uget_borrowed(v_as_2650_, v_i_2652_);
lean_inc(v___y_2657_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2654_);
lean_inc(v_a_2661_);
v___x_2662_ = lean_infer_type(v_a_2661_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
lean_inc_ref(v_fs_2649_);
lean_inc_ref(v___x_2648_);
lean_inc_ref(v___x_2647_);
lean_inc(v___x_2646_);
v___x_2664_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2646_, v___x_2647_, v___x_2648_, v_fs_2649_, v_a_2663_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = l_Lean_Expr_app___override(v_b_2653_, v_a_2665_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = lean_usize_add(v_i_2652_, v___x_2667_);
v_i_2652_ = v___x_2668_;
v_b_2653_ = v___x_2666_;
goto _start;
}
else
{
lean_dec_ref(v_b_2653_);
lean_dec_ref(v_fs_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v___x_2647_);
lean_dec(v___x_2646_);
return v___x_2664_;
}
}
else
{
lean_dec_ref(v_b_2653_);
lean_dec_ref(v_fs_2649_);
lean_dec_ref(v___x_2648_);
lean_dec_ref(v___x_2647_);
lean_dec(v___x_2646_);
return v___x_2662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2670_, lean_object* v___x_2671_, lean_object* v___x_2672_, lean_object* v_fs_2673_, lean_object* v_as_2674_, lean_object* v_sz_2675_, lean_object* v_i_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
size_t v_sz_boxed_2683_; size_t v_i_boxed_2684_; lean_object* v_res_2685_; 
v_sz_boxed_2683_ = lean_unbox_usize(v_sz_2675_);
lean_dec(v_sz_2675_);
v_i_boxed_2684_ = lean_unbox_usize(v_i_2676_);
lean_dec(v_i_2676_);
v_res_2685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2670_, v___x_2671_, v___x_2672_, v_fs_2673_, v_as_2674_, v_sz_boxed_2683_, v_i_boxed_2684_, v_b_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_as_2674_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2686_, lean_object* v___x_2687_, uint8_t v___x_2688_, lean_object* v_targs_2689_, lean_object* v_x_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = l_Lean_mkAppN(v_a_2686_, v_targs_2689_);
v___x_2697_ = l_Lean_mkAppN(v___x_2687_, v_targs_2689_);
v___x_2698_ = l_Lean_Meta_mkPProd(v___x_2696_, v___x_2697_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = 0;
v___x_2701_ = 1;
v___x_2702_ = l_Lean_Meta_mkLambdaFVars(v_targs_2689_, v_a_2699_, v___x_2700_, v___x_2688_, v___x_2700_, v___x_2688_, v___x_2701_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v___x_2702_;
}
else
{
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2703_, lean_object* v___x_2704_, lean_object* v___x_2705_, lean_object* v_targs_2706_, lean_object* v_x_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
uint8_t v___x_33314__boxed_2713_; lean_object* v_res_2714_; 
v___x_33314__boxed_2713_ = lean_unbox(v___x_2705_);
v_res_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2703_, v___x_2704_, v___x_33314__boxed_2713_, v_targs_2706_, v_x_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v_x_2707_);
lean_dec_ref(v_targs_2706_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2715_, lean_object* v___x_2716_, lean_object* v_as_2717_, size_t v_sz_2718_, size_t v_i_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_usize_dec_lt(v_i_2719_, v_sz_2718_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_b_2720_);
return v___x_2727_;
}
else
{
lean_object* v_snd_2728_; lean_object* v_fst_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2786_; 
v_snd_2728_ = lean_ctor_get(v_b_2720_, 1);
v_fst_2729_ = lean_ctor_get(v_b_2720_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_b_2720_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2731_ = v_b_2720_;
v_isShared_2732_ = v_isSharedCheck_2786_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_snd_2728_);
lean_inc(v_fst_2729_);
lean_dec(v_b_2720_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2786_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_array_2733_; lean_object* v_start_2734_; lean_object* v_stop_2735_; uint8_t v___x_2736_; 
v_array_2733_ = lean_ctor_get(v_snd_2728_, 0);
v_start_2734_ = lean_ctor_get(v_snd_2728_, 1);
v_stop_2735_ = lean_ctor_get(v_snd_2728_, 2);
v___x_2736_ = lean_nat_dec_lt(v_start_2734_, v_stop_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2738_; 
if (v_isShared_2732_ == 0)
{
v___x_2738_ = v___x_2731_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_fst_2729_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_snd_2728_);
v___x_2738_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
}
else
{
lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_stop_2735_);
lean_inc(v_start_2734_);
lean_inc_ref(v_array_2733_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_snd_2728_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; lean_object* v_unused_2785_; 
v_unused_2783_ = lean_ctor_get(v_snd_2728_, 2);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_snd_2728_, 1);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_snd_2728_, 0);
lean_dec(v_unused_2785_);
v___x_2742_ = v_snd_2728_;
v_isShared_2743_ = v_isSharedCheck_2782_;
goto v_resetjp_2741_;
}
else
{
lean_dec(v_snd_2728_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2782_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint8_t v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2744_ = lean_nat_dec_lt(v___x_2715_, v___x_2716_);
v_a_2745_ = lean_array_uget_borrowed(v_as_2717_, v_i_2719_);
v___x_2746_ = lean_array_fget_borrowed(v_array_2733_, v_start_2734_);
v___x_2747_ = lean_box(v___x_2744_);
lean_inc(v___x_2746_);
lean_inc(v_a_2745_);
v___f_2748_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2748_, 0, v_a_2745_);
lean_closure_set(v___f_2748_, 1, v___x_2746_);
lean_closure_set(v___f_2748_, 2, v___x_2747_);
v___x_2749_ = lean_unsigned_to_nat(1u);
v___x_2750_ = lean_nat_add(v_start_2734_, v___x_2749_);
lean_dec(v_start_2734_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2750_);
v___x_2752_ = v___x_2742_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_array_2733_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_stop_2735_);
v___x_2752_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v_a_2745_);
v___x_2753_ = lean_infer_type(v_a_2745_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = 0;
v___x_2756_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2754_, v___f_2748_, v___x_2755_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = l_Lean_Expr_app___override(v_fst_2729_, v_a_2757_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 1, v___x_2752_);
lean_ctor_set(v___x_2731_, 0, v___x_2758_);
v___x_2760_ = v___x_2731_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2758_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2752_);
v___x_2760_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
size_t v___x_2761_; size_t v___x_2762_; 
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2719_, v___x_2761_);
v_i_2719_ = v___x_2762_;
v_b_2720_ = v___x_2760_;
goto _start;
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v___x_2752_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
v_a_2765_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2756_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2756_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v___x_2752_);
lean_dec_ref(v___f_2748_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
v_a_2773_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2753_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2753_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_as_2789_, lean_object* v_sz_2790_, lean_object* v_i_2791_, lean_object* v_b_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
size_t v_sz_boxed_2798_; size_t v_i_boxed_2799_; lean_object* v_res_2800_; 
v_sz_boxed_2798_ = lean_unbox_usize(v_sz_2790_);
lean_dec(v_sz_2790_);
v_i_boxed_2799_ = lean_unbox_usize(v_i_2791_);
lean_dec(v_i_2791_);
v_res_2800_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2787_, v___x_2788_, v_as_2789_, v_sz_boxed_2798_, v_i_boxed_2799_, v_b_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec_ref(v_as_2789_);
lean_dec(v___x_2788_);
lean_dec(v___x_2787_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2803_, v_sz_2802_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_b_2804_);
return v___x_2811_;
}
else
{
lean_object* v_a_2812_; lean_object* v_toInductionSubgoal_2813_; lean_object* v_mvarId_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_a_2812_ = lean_array_uget_borrowed(v_as_2801_, v_i_2803_);
v_toInductionSubgoal_2813_ = lean_ctor_get(v_a_2812_, 0);
v_mvarId_2814_ = lean_ctor_get(v_toInductionSubgoal_2813_, 0);
v___x_2815_ = 0;
v___x_2816_ = lean_box(0);
lean_inc(v_mvarId_2814_);
v___x_2817_ = l_Lean_MVarId_refl(v_mvarId_2814_, v___x_2815_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2817_) == 0)
{
size_t v___x_2818_; size_t v___x_2819_; 
lean_dec_ref_known(v___x_2817_, 1);
v___x_2818_ = ((size_t)1ULL);
v___x_2819_ = lean_usize_add(v_i_2803_, v___x_2818_);
v_i_2803_ = v___x_2819_;
v_b_2804_ = v___x_2816_;
goto _start;
}
else
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2821_, lean_object* v_sz_2822_, lean_object* v_i_2823_, lean_object* v_b_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
size_t v_sz_boxed_2830_; size_t v_i_boxed_2831_; lean_object* v_res_2832_; 
v_sz_boxed_2830_ = lean_unbox_usize(v_sz_2822_);
lean_dec(v_sz_2822_);
v_i_boxed_2831_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2821_, v_sz_boxed_2830_, v_i_boxed_2831_, v_b_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v_as_2821_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2833_, lean_object* v_tail_2834_, lean_object* v_recName_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v___x_2844_, lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v_val_2847_, uint8_t v___x_2848_, lean_object* v_brecOnGoName_2849_, lean_object* v_levelParams_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v_brecOnName_2853_, lean_object* v_brecOnEqName_2854_, lean_object* v_fs_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; size_t v_sz_2865_; size_t v___x_2866_; lean_object* v___x_2867_; 
lean_inc(v___x_2833_);
v___x_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2833_);
lean_ctor_set(v___x_2861_, 1, v_tail_2834_);
v___x_2862_ = l_Lean_Expr_const___override(v_recName_2835_, v___x_2861_);
v___x_2863_ = l_Lean_mkAppN(v___x_2862_, v___x_2836_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v___x_2837_);
v_sz_2865_ = lean_array_size(v___x_2838_);
v___x_2866_ = ((size_t)0ULL);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2839_, v___x_2840_, v___x_2838_, v_sz_2865_, v___x_2866_, v___x_2864_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v_fst_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_3238_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v_fst_2869_ = lean_ctor_get(v_a_2868_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_a_2868_, 1);
lean_dec(v_unused_3239_);
v___x_2871_ = v_a_2868_;
v_isShared_2872_ = v_isSharedCheck_3238_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_fst_2869_);
lean_dec(v_a_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_3238_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
size_t v_sz_2873_; lean_object* v___x_2874_; 
v_sz_2873_ = lean_array_size(v___x_2841_);
lean_inc_ref(v_fs_2855_);
lean_inc_ref(v___x_2842_);
lean_inc_ref(v___x_2838_);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2833_, v___x_2838_, v___x_2842_, v_fs_2855_, v___x_2841_, v_sz_2873_, v___x_2866_, v_fst_2869_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = l_Lean_mkAppN(v_a_2875_, v___x_2843_);
lean_inc_ref_n(v___x_2844_, 3);
v___x_2877_ = l_Lean_Expr_app___override(v___x_2876_, v___x_2844_);
v___x_2878_ = l_Array_append___redArg(v___x_2836_, v___x_2838_);
v___x_2879_ = l_Array_append___redArg(v___x_2878_, v___x_2843_);
v___x_2880_ = lean_mk_empty_array_with_capacity(v___x_2845_);
v___x_2881_ = lean_array_push(v___x_2880_, v___x_2844_);
v___x_2882_ = l_Array_append___redArg(v___x_2879_, v___x_2881_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = l_Array_append___redArg(v___x_2882_, v_fs_2855_);
v___x_2884_ = lean_array_get(v___x_2846_, v___x_2838_, v_val_2847_);
lean_dec_ref(v___x_2838_);
v___x_2885_ = lean_array_push(v___x_2843_, v___x_2844_);
v___x_2886_ = l_Lean_mkAppN(v___x_2884_, v___x_2885_);
v___x_2887_ = lean_array_get(v___x_2846_, v___x_2842_, v_val_2847_);
lean_dec_ref(v___x_2842_);
v___x_2888_ = l_Lean_mkAppN(v___x_2887_, v___x_2885_);
lean_inc_ref(v___x_2886_);
v___x_2889_ = l_Lean_Meta_mkPProd(v___x_2886_, v___x_2888_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; uint8_t v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2891_ = 0;
v___x_2892_ = 1;
v___x_2893_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v_a_2890_, v___x_2891_, v___x_2848_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v___x_2877_, v___x_2891_, v___x_2848_, v___x_2891_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_3205_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = lean_box(1);
lean_inc(v_levelParams_2850_);
lean_inc(v_brecOnGoName_2849_);
v___x_2898_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2849_, v_levelParams_2850_, v_a_2894_, v_a_2896_, v___x_2897_, v___y_2859_);
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_3205_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_3205_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
lean_inc(v_a_2899_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set_tag(v___x_2901_, 1);
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_3204_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_addDecl(v___x_2904_, v___x_2891_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_toConstantVal_2906_; lean_object* v_name_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref_known(v___x_2905_, 1);
v_toConstantVal_2906_ = lean_ctor_get(v_a_2899_, 0);
lean_inc_ref(v_toConstantVal_2906_);
lean_dec(v_a_2899_);
v_name_2907_ = lean_ctor_get(v_toConstantVal_2906_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_toConstantVal_2906_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; lean_object* v_unused_3203_; 
v_unused_3202_ = lean_ctor_get(v_toConstantVal_2906_, 2);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_toConstantVal_2906_, 1);
lean_dec(v_unused_3203_);
v___x_2909_ = v_toConstantVal_2906_;
v_isShared_2910_ = v_isSharedCheck_3201_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_name_2907_);
lean_dec(v_toConstantVal_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3201_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_env_2913_; lean_object* v_nextMacroScope_2914_; lean_object* v_ngen_2915_; lean_object* v_auxDeclNGen_2916_; lean_object* v_traceState_2917_; lean_object* v_recordedDeps_2918_; lean_object* v_messages_2919_; lean_object* v_infoState_2920_; lean_object* v_snapshotTasks_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3199_; 
lean_inc(v_name_2907_);
v___x_2911_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2907_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec_ref(v___x_2911_);
v___x_2912_ = lean_st_ref_take(v___y_2859_);
v_env_2913_ = lean_ctor_get(v___x_2912_, 0);
v_nextMacroScope_2914_ = lean_ctor_get(v___x_2912_, 1);
v_ngen_2915_ = lean_ctor_get(v___x_2912_, 2);
v_auxDeclNGen_2916_ = lean_ctor_get(v___x_2912_, 3);
v_traceState_2917_ = lean_ctor_get(v___x_2912_, 4);
v_recordedDeps_2918_ = lean_ctor_get(v___x_2912_, 6);
v_messages_2919_ = lean_ctor_get(v___x_2912_, 7);
v_infoState_2920_ = lean_ctor_get(v___x_2912_, 8);
v_snapshotTasks_2921_ = lean_ctor_get(v___x_2912_, 9);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_2912_, 5);
lean_dec(v_unused_3200_);
v___x_2923_ = v___x_2912_;
v_isShared_2924_ = v_isSharedCheck_3199_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_snapshotTasks_2921_);
lean_inc(v_infoState_2920_);
lean_inc(v_messages_2919_);
lean_inc(v_recordedDeps_2918_);
lean_inc(v_traceState_2917_);
lean_inc(v_auxDeclNGen_2916_);
lean_inc(v_ngen_2915_);
lean_inc(v_nextMacroScope_2914_);
lean_inc(v_env_2913_);
lean_dec(v___x_2912_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3199_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2925_ = l_Lean_addProtected(v_env_2913_, v_name_2907_);
v___x_2926_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_2927_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 5, v___x_2927_);
lean_ctor_set(v___x_2923_, 0, v___x_2925_);
v___x_2929_ = v___x_2923_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_nextMacroScope_2914_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_ngen_2915_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_auxDeclNGen_2916_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_traceState_2917_);
lean_ctor_set(v_reuseFailAlloc_3198_, 5, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3198_, 6, v_recordedDeps_2918_);
lean_ctor_set(v_reuseFailAlloc_3198_, 7, v_messages_2919_);
lean_ctor_set(v_reuseFailAlloc_3198_, 8, v_infoState_2920_);
lean_ctor_set(v_reuseFailAlloc_3198_, 9, v_snapshotTasks_2921_);
v___x_2929_ = v_reuseFailAlloc_3198_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v_mctx_2932_; lean_object* v_zetaDeltaFVarIds_2933_; lean_object* v_postponed_2934_; lean_object* v_diag_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3196_; 
v___x_2930_ = lean_st_ref_put(v___y_2859_, v___x_2929_);
v___x_2931_ = lean_st_ref_take(v___y_2857_);
v_mctx_2932_ = lean_ctor_get(v___x_2931_, 0);
v_zetaDeltaFVarIds_2933_ = lean_ctor_get(v___x_2931_, 2);
v_postponed_2934_ = lean_ctor_get(v___x_2931_, 3);
v_diag_2935_ = lean_ctor_get(v___x_2931_, 4);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v___x_2931_, 1);
lean_dec(v_unused_3197_);
v___x_2937_ = v___x_2931_;
v_isShared_2938_ = v_isSharedCheck_3196_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_diag_2935_);
lean_inc(v_postponed_2934_);
lean_inc(v_zetaDeltaFVarIds_2933_);
lean_inc(v_mctx_2932_);
lean_dec(v___x_2931_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3196_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2939_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
v___x_2940_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
lean_inc(v___x_2851_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 2, v___x_2851_);
lean_ctor_set(v___x_2909_, 1, v___x_2926_);
lean_ctor_set(v___x_2909_, 0, v___x_2926_);
v___x_2942_ = v___x_2909_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v___x_2851_);
v___x_2942_ = v_reuseFailAlloc_3195_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2943_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2939_);
lean_ctor_set(v___x_2943_, 1, v___x_2926_);
lean_ctor_set(v___x_2943_, 2, v___x_2940_);
lean_ctor_set(v___x_2943_, 3, v___x_2926_);
lean_ctor_set(v___x_2943_, 4, v___x_2926_);
lean_ctor_set(v___x_2943_, 5, v___x_2926_);
lean_ctor_set(v___x_2943_, 6, v___x_2926_);
lean_ctor_set(v___x_2943_, 7, v___x_2942_);
lean_inc_ref(v___x_2943_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2943_);
v___x_2945_ = v___x_2937_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_mctx_2932_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_zetaDeltaFVarIds_2933_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_postponed_2934_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v_diag_2935_);
v___x_2945_ = v_reuseFailAlloc_3194_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2946_ = lean_st_ref_put(v___y_2857_, v___x_2945_);
lean_inc(v___x_2852_);
v___x_2947_ = l_Lean_Expr_const___override(v_brecOnGoName_2849_, v___x_2852_);
v___x_2948_ = l_Lean_mkAppN(v___x_2947_, v___x_2883_);
lean_inc_ref(v___x_2948_);
v___x_2949_ = l_Lean_Meta_mkPProdFstM(v___x_2948_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v_a_2950_, v___x_2891_, v___x_2848_, v___x_2891_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2953_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v___x_2886_, v___x_2891_, v___x_2848_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_3169_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
lean_inc(v_levelParams_2850_);
v___x_2955_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2853_, v_levelParams_2850_, v_a_2954_, v_a_2952_, v___x_2897_, v___y_2859_);
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_3169_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_3169_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
lean_inc(v_a_2956_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 1);
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_3168_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Lean_addDecl(v___x_2961_, v___x_2891_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_toConstantVal_2963_; lean_object* v_name_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3165_; 
lean_dec_ref_known(v___x_2962_, 1);
v_toConstantVal_2963_ = lean_ctor_get(v_a_2956_, 0);
lean_inc_ref(v_toConstantVal_2963_);
lean_dec(v_a_2956_);
v_name_2964_ = lean_ctor_get(v_toConstantVal_2963_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_toConstantVal_2963_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; lean_object* v_unused_3167_; 
v_unused_3166_ = lean_ctor_get(v_toConstantVal_2963_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_toConstantVal_2963_, 1);
lean_dec(v_unused_3167_);
v___x_2966_ = v_toConstantVal_2963_;
v_isShared_2967_ = v_isSharedCheck_3165_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_name_2964_);
lean_dec(v_toConstantVal_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3165_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_env_2970_; lean_object* v_nextMacroScope_2971_; lean_object* v_ngen_2972_; lean_object* v_auxDeclNGen_2973_; lean_object* v_traceState_2974_; lean_object* v_recordedDeps_2975_; lean_object* v_messages_2976_; lean_object* v_infoState_2977_; lean_object* v_snapshotTasks_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3163_; 
lean_inc(v_name_2964_);
v___x_2968_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2964_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec_ref(v___x_2968_);
v___x_2969_ = lean_st_ref_take(v___y_2859_);
v_env_2970_ = lean_ctor_get(v___x_2969_, 0);
v_nextMacroScope_2971_ = lean_ctor_get(v___x_2969_, 1);
v_ngen_2972_ = lean_ctor_get(v___x_2969_, 2);
v_auxDeclNGen_2973_ = lean_ctor_get(v___x_2969_, 3);
v_traceState_2974_ = lean_ctor_get(v___x_2969_, 4);
v_recordedDeps_2975_ = lean_ctor_get(v___x_2969_, 6);
v_messages_2976_ = lean_ctor_get(v___x_2969_, 7);
v_infoState_2977_ = lean_ctor_get(v___x_2969_, 8);
v_snapshotTasks_2978_ = lean_ctor_get(v___x_2969_, 9);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v___x_2969_, 5);
lean_dec(v_unused_3164_);
v___x_2980_ = v___x_2969_;
v_isShared_2981_ = v_isSharedCheck_3163_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_snapshotTasks_2978_);
lean_inc(v_infoState_2977_);
lean_inc(v_messages_2976_);
lean_inc(v_recordedDeps_2975_);
lean_inc(v_traceState_2974_);
lean_inc(v_auxDeclNGen_2973_);
lean_inc(v_ngen_2972_);
lean_inc(v_nextMacroScope_2971_);
lean_inc(v_env_2970_);
lean_dec(v___x_2969_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3163_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2984_; 
lean_inc(v_name_2964_);
v___x_2982_ = l_Lean_markAuxRecursor(v_env_2970_, v_name_2964_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 5, v___x_2927_);
lean_ctor_set(v___x_2980_, 0, v___x_2982_);
v___x_2984_ = v___x_2980_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_nextMacroScope_2971_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_ngen_2972_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_auxDeclNGen_2973_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v_traceState_2974_);
lean_ctor_set(v_reuseFailAlloc_3162_, 5, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3162_, 6, v_recordedDeps_2975_);
lean_ctor_set(v_reuseFailAlloc_3162_, 7, v_messages_2976_);
lean_ctor_set(v_reuseFailAlloc_3162_, 8, v_infoState_2977_);
lean_ctor_set(v_reuseFailAlloc_3162_, 9, v_snapshotTasks_2978_);
v___x_2984_ = v_reuseFailAlloc_3162_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_mctx_2987_; lean_object* v_zetaDeltaFVarIds_2988_; lean_object* v_postponed_2989_; lean_object* v_diag_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3160_; 
v___x_2985_ = lean_st_ref_put(v___y_2859_, v___x_2984_);
v___x_2986_ = lean_st_ref_take(v___y_2857_);
v_mctx_2987_ = lean_ctor_get(v___x_2986_, 0);
v_zetaDeltaFVarIds_2988_ = lean_ctor_get(v___x_2986_, 2);
v_postponed_2989_ = lean_ctor_get(v___x_2986_, 3);
v_diag_2990_ = lean_ctor_get(v___x_2986_, 4);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v___x_2986_, 1);
lean_dec(v_unused_3161_);
v___x_2992_ = v___x_2986_;
v_isShared_2993_ = v_isSharedCheck_3160_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_diag_2990_);
lean_inc(v_postponed_2989_);
lean_inc(v_zetaDeltaFVarIds_2988_);
lean_inc(v_mctx_2987_);
lean_dec(v___x_2986_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3160_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
lean_inc_ref(v___x_2943_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_2943_);
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_mctx_2987_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_zetaDeltaFVarIds_2988_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_postponed_2989_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_diag_2990_);
v___x_2995_ = v_reuseFailAlloc_3159_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_ngen_3000_; lean_object* v_auxDeclNGen_3001_; lean_object* v_traceState_3002_; lean_object* v_recordedDeps_3003_; lean_object* v_messages_3004_; lean_object* v_infoState_3005_; lean_object* v_snapshotTasks_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3157_; 
v___x_2996_ = lean_st_ref_put(v___y_2857_, v___x_2995_);
v___x_2997_ = lean_st_ref_take(v___y_2859_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3000_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3001_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3002_ = lean_ctor_get(v___x_2997_, 4);
v_recordedDeps_3003_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3004_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3005_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3006_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3158_);
v___x_3008_ = v___x_2997_;
v_isShared_3009_ = v_isSharedCheck_3157_;
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
v_isShared_3009_ = v_isSharedCheck_3157_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_inc(v_name_2964_);
v___x_3010_ = l_Lean_addProtected(v_env_2998_, v_name_2964_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 5, v___x_2927_);
lean_ctor_set(v___x_3008_, 0, v___x_3010_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_auxDeclNGen_3001_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_traceState_3002_);
lean_ctor_set(v_reuseFailAlloc_3156_, 5, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3156_, 6, v_recordedDeps_3003_);
lean_ctor_set(v_reuseFailAlloc_3156_, 7, v_messages_3004_);
lean_ctor_set(v_reuseFailAlloc_3156_, 8, v_infoState_3005_);
lean_ctor_set(v_reuseFailAlloc_3156_, 9, v_snapshotTasks_3006_);
v___x_3012_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v_mctx_3015_; lean_object* v_zetaDeltaFVarIds_3016_; lean_object* v_postponed_3017_; lean_object* v_diag_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3154_; 
v___x_3013_ = lean_st_ref_put(v___y_2859_, v___x_3012_);
v___x_3014_ = lean_st_ref_take(v___y_2857_);
v_mctx_3015_ = lean_ctor_get(v___x_3014_, 0);
v_zetaDeltaFVarIds_3016_ = lean_ctor_get(v___x_3014_, 2);
v_postponed_3017_ = lean_ctor_get(v___x_3014_, 3);
v_diag_3018_ = lean_ctor_get(v___x_3014_, 4);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v___x_3014_, 1);
lean_dec(v_unused_3155_);
v___x_3020_ = v___x_3014_;
v_isShared_3021_ = v_isSharedCheck_3154_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_diag_3018_);
lean_inc(v_postponed_3017_);
lean_inc(v_zetaDeltaFVarIds_3016_);
lean_inc(v_mctx_3015_);
lean_dec(v___x_3014_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3154_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
lean_inc_ref(v___x_2943_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 1, v___x_2943_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_mctx_3015_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_3153_, 2, v_zetaDeltaFVarIds_3016_);
lean_ctor_set(v_reuseFailAlloc_3153_, 3, v_postponed_3017_);
lean_ctor_set(v_reuseFailAlloc_3153_, 4, v_diag_3018_);
v___x_3023_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3024_ = lean_st_ref_put(v___y_2857_, v___x_3023_);
v___x_3025_ = l_Lean_Expr_const___override(v_name_2964_, v___x_2852_);
v___x_3026_ = l_Lean_mkAppN(v___x_3025_, v___x_2883_);
v___x_3027_ = lean_array_get(v___x_2846_, v_fs_2855_, v_val_2847_);
lean_dec_ref(v_fs_2855_);
v___x_3028_ = l_Lean_mkAppN(v___x_3027_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_3029_ = l_Lean_Meta_mkPProdSndM(v___x_2948_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = l_Lean_Expr_app___override(v___x_3028_, v_a_3030_);
v___x_3032_ = l_Lean_Meta_mkEq(v___x_3026_, v___x_3031_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc_n(v_a_3033_, 2);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = lean_box(0);
v___x_3035_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3033_, v___x_3034_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = l_Lean_Expr_mvarId_x21(v_a_3036_);
v___x_3038_ = l_Lean_Expr_fvarId_x21(v___x_2844_);
lean_dec_ref(v___x_2844_);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_2851_);
lean_dec(v___x_2851_);
v___x_3040_ = lean_box(0);
v___x_3041_ = l_Lean_MVarId_cases(v___x_3037_, v___x_3038_, v___x_3039_, v___x_2891_, v___x_3040_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; size_t v_sz_3044_; lean_object* v___x_3045_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = lean_box(0);
v_sz_3044_ = lean_array_size(v_a_3042_);
v___x_3045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3042_, v_sz_3044_, v___x_2866_, v___x_3043_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v_a_3042_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v___x_3046_; lean_object* v_a_3047_; lean_object* v___x_3048_; 
lean_dec_ref_known(v___x_3045_, 1);
v___x_3046_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_3036_, v___y_2857_);
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref(v___x_3046_);
v___x_3048_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v_a_3033_, v___x_2891_, v___x_2848_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v_a_3047_, v___x_2891_, v___x_2848_, v___x_2891_, v___x_2848_, v___x_2892_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec_ref(v___x_2883_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
lean_inc(v_brecOnEqName_2854_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 2, v_a_3049_);
lean_ctor_set(v___x_2966_, 1, v_levelParams_2850_);
lean_ctor_set(v___x_2966_, 0, v_brecOnEqName_2854_);
v___x_3053_ = v___x_2966_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_brecOnEqName_2854_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_levelParams_2850_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_a_3049_);
v___x_3053_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3054_ = lean_box(0);
lean_inc(v_brecOnEqName_2854_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 1);
lean_ctor_set(v___x_2871_, 1, v___x_3054_);
lean_ctor_set(v___x_2871_, 0, v_brecOnEqName_2854_);
v___x_3056_ = v___x_2871_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_brecOnEqName_2854_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v_a_3059_; lean_object* v___x_3060_; 
v___x_3057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3053_);
lean_ctor_set(v___x_3057_, 1, v_a_3051_);
lean_ctor_set(v___x_3057_, 2, v___x_3056_);
v___x_3058_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3057_, v___y_2859_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l_Lean_addDecl(v_a_3059_, v___x_2891_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3101_; 
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3060_, 0);
lean_dec(v_unused_3102_);
v___x_3062_ = v___x_3060_;
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
else
{
lean_dec(v___x_3060_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v_env_3065_; lean_object* v_nextMacroScope_3066_; lean_object* v_ngen_3067_; lean_object* v_auxDeclNGen_3068_; lean_object* v_traceState_3069_; lean_object* v_recordedDeps_3070_; lean_object* v_messages_3071_; lean_object* v_infoState_3072_; lean_object* v_snapshotTasks_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3099_; 
v___x_3064_ = lean_st_ref_take(v___y_2859_);
v_env_3065_ = lean_ctor_get(v___x_3064_, 0);
v_nextMacroScope_3066_ = lean_ctor_get(v___x_3064_, 1);
v_ngen_3067_ = lean_ctor_get(v___x_3064_, 2);
v_auxDeclNGen_3068_ = lean_ctor_get(v___x_3064_, 3);
v_traceState_3069_ = lean_ctor_get(v___x_3064_, 4);
v_recordedDeps_3070_ = lean_ctor_get(v___x_3064_, 6);
v_messages_3071_ = lean_ctor_get(v___x_3064_, 7);
v_infoState_3072_ = lean_ctor_get(v___x_3064_, 8);
v_snapshotTasks_3073_ = lean_ctor_get(v___x_3064_, 9);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3064_, 5);
lean_dec(v_unused_3100_);
v___x_3075_ = v___x_3064_;
v_isShared_3076_ = v_isSharedCheck_3099_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_snapshotTasks_3073_);
lean_inc(v_infoState_3072_);
lean_inc(v_messages_3071_);
lean_inc(v_recordedDeps_3070_);
lean_inc(v_traceState_3069_);
lean_inc(v_auxDeclNGen_3068_);
lean_inc(v_ngen_3067_);
lean_inc(v_nextMacroScope_3066_);
lean_inc(v_env_3065_);
lean_dec(v___x_3064_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3099_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3077_ = l_Lean_addProtected(v_env_3065_, v_brecOnEqName_2854_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 5, v___x_2927_);
lean_ctor_set(v___x_3075_, 0, v___x_3077_);
v___x_3079_ = v___x_3075_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3098_, 1, v_nextMacroScope_3066_);
lean_ctor_set(v_reuseFailAlloc_3098_, 2, v_ngen_3067_);
lean_ctor_set(v_reuseFailAlloc_3098_, 3, v_auxDeclNGen_3068_);
lean_ctor_set(v_reuseFailAlloc_3098_, 4, v_traceState_3069_);
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_recordedDeps_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_messages_3071_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_infoState_3072_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_snapshotTasks_3073_);
v___x_3079_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_mctx_3082_; lean_object* v_zetaDeltaFVarIds_3083_; lean_object* v_postponed_3084_; lean_object* v_diag_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3096_; 
v___x_3080_ = lean_st_ref_put(v___y_2859_, v___x_3079_);
v___x_3081_ = lean_st_ref_take(v___y_2857_);
v_mctx_3082_ = lean_ctor_get(v___x_3081_, 0);
v_zetaDeltaFVarIds_3083_ = lean_ctor_get(v___x_3081_, 2);
v_postponed_3084_ = lean_ctor_get(v___x_3081_, 3);
v_diag_3085_ = lean_ctor_get(v___x_3081_, 4);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v___x_3081_, 1);
lean_dec(v_unused_3097_);
v___x_3087_ = v___x_3081_;
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_diag_3085_);
lean_inc(v_postponed_3084_);
lean_inc(v_zetaDeltaFVarIds_3083_);
lean_inc(v_mctx_3082_);
lean_dec(v___x_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3096_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_2943_);
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_mctx_3082_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_2943_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_zetaDeltaFVarIds_3083_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_postponed_3084_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_diag_3085_);
v___x_3090_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = lean_st_ref_put(v___y_2857_, v___x_3090_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3043_);
v___x_3093_ = v___x_3062_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3043_);
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
}
}
}
else
{
lean_dec_ref_known(v___x_2943_, 8);
lean_dec(v_brecOnEqName_2854_);
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3049_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_levelParams_2850_);
v_a_3105_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3050_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3050_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v_a_3047_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_levelParams_2850_);
v_a_3113_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3048_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3048_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
else
{
lean_dec(v_a_3036_);
lean_dec(v_a_3033_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_levelParams_2850_);
return v___x_3045_;
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3036_);
lean_dec(v_a_3033_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_levelParams_2850_);
v_a_3121_ = lean_ctor_get(v___x_3041_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3041_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3041_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3041_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_a_3033_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3129_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3035_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3035_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3137_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3032_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3032_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___x_3028_);
lean_dec_ref(v___x_3026_);
lean_del_object(v___x_2966_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3145_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3029_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3029_);
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
lean_dec(v_a_2956_);
lean_dec_ref(v___x_2948_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec(v_a_2952_);
lean_dec_ref(v___x_2948_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3170_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_2953_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_2953_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref(v___x_2948_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3178_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_2951_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_2951_);
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
lean_dec_ref(v___x_2948_);
lean_dec_ref_known(v___x_2943_, 8);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec_ref(v___x_2844_);
v_a_3186_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_2949_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_2949_);
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
}
}
}
}
}
}
else
{
lean_dec(v_a_2899_);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_2894_);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
v_a_3206_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_2895_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_2895_);
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
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
v_a_3214_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_2893_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_2893_);
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
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
v_a_3222_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_2889_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_2889_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v___x_3227_; 
if (v_isShared_3225_ == 0)
{
v___x_3227_ = v___x_3224_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_a_3222_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_del_object(v___x_2871_);
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2842_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2836_);
v_a_3230_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_2874_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_2874_);
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
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v_fs_2855_);
lean_dec(v_brecOnEqName_2854_);
lean_dec(v_brecOnName_2853_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
lean_dec(v_levelParams_2850_);
lean_dec(v_brecOnGoName_2849_);
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2842_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2836_);
lean_dec(v___x_2833_);
v_a_3240_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_2867_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_2867_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3248_ = _args[0];
lean_object* v_tail_3249_ = _args[1];
lean_object* v_recName_3250_ = _args[2];
lean_object* v___x_3251_ = _args[3];
lean_object* v___x_3252_ = _args[4];
lean_object* v___x_3253_ = _args[5];
lean_object* v___x_3254_ = _args[6];
lean_object* v___x_3255_ = _args[7];
lean_object* v___x_3256_ = _args[8];
lean_object* v___x_3257_ = _args[9];
lean_object* v___x_3258_ = _args[10];
lean_object* v___x_3259_ = _args[11];
lean_object* v___x_3260_ = _args[12];
lean_object* v___x_3261_ = _args[13];
lean_object* v_val_3262_ = _args[14];
lean_object* v___x_3263_ = _args[15];
lean_object* v_brecOnGoName_3264_ = _args[16];
lean_object* v_levelParams_3265_ = _args[17];
lean_object* v___x_3266_ = _args[18];
lean_object* v___x_3267_ = _args[19];
lean_object* v_brecOnName_3268_ = _args[20];
lean_object* v_brecOnEqName_3269_ = _args[21];
lean_object* v_fs_3270_ = _args[22];
lean_object* v___y_3271_ = _args[23];
lean_object* v___y_3272_ = _args[24];
lean_object* v___y_3273_ = _args[25];
lean_object* v___y_3274_ = _args[26];
lean_object* v___y_3275_ = _args[27];
_start:
{
uint8_t v___x_33540__boxed_3276_; lean_object* v_res_3277_; 
v___x_33540__boxed_3276_ = lean_unbox(v___x_3263_);
v_res_3277_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3248_, v_tail_3249_, v_recName_3250_, v___x_3251_, v___x_3252_, v___x_3253_, v___x_3254_, v___x_3255_, v___x_3256_, v___x_3257_, v___x_3258_, v___x_3259_, v___x_3260_, v___x_3261_, v_val_3262_, v___x_33540__boxed_3276_, v_brecOnGoName_3264_, v_levelParams_3265_, v___x_3266_, v___x_3267_, v_brecOnName_3268_, v_brecOnEqName_3269_, v_fs_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_val_3262_);
lean_dec_ref(v___x_3261_);
lean_dec(v___x_3260_);
lean_dec_ref(v___x_3256_);
lean_dec(v___x_3255_);
lean_dec(v___x_3254_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3278_, lean_object* v_a_3279_, uint8_t v___x_3280_, lean_object* v_f_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; 
lean_inc_ref(v_targs_3278_);
v___x_3287_ = lean_array_push(v_targs_3278_, v_f_3281_);
v___x_3288_ = l_Lean_mkAppN(v_a_3279_, v_targs_3278_);
lean_dec_ref(v_targs_3278_);
v___x_3289_ = 0;
v___x_3290_ = 1;
v___x_3291_ = l_Lean_Meta_mkForallFVars(v___x_3287_, v___x_3288_, v___x_3289_, v___x_3280_, v___x_3280_, v___x_3290_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec_ref(v___x_3287_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3292_, lean_object* v_a_3293_, lean_object* v___x_3294_, lean_object* v_f_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
uint8_t v___x_34261__boxed_3301_; lean_object* v_res_3302_; 
v___x_34261__boxed_3301_ = lean_unbox(v___x_3294_);
v_res_3302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3292_, v_a_3293_, v___x_34261__boxed_3301_, v_f_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3306_, uint8_t v___x_3307_, lean_object* v___x_3308_, lean_object* v_targs_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3316_ = lean_box(v___x_3307_);
lean_inc_ref(v_targs_3309_);
v___f_3317_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3317_, 0, v_targs_3309_);
lean_closure_set(v___f_3317_, 1, v_a_3306_);
lean_closure_set(v___f_3317_, 2, v___x_3316_);
v___x_3318_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3319_ = l_Lean_mkAppN(v___x_3308_, v_targs_3309_);
lean_dec_ref(v_targs_3309_);
v___x_3320_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3318_, v___x_3319_, v___f_3317_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v_targs_3324_, lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
uint8_t v___x_34295__boxed_3331_; lean_object* v_res_3332_; 
v___x_34295__boxed_3331_ = lean_unbox(v___x_3322_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3321_, v___x_34295__boxed_3331_, v___x_3323_, v_targs_3324_, v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_x_3325_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3333_, lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v___x_3340_; 
v___x_3340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3340_, 0, v_a_3333_);
return v___x_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3341_, lean_object* v_x_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_res_3348_; 
v_res_3348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3341_, v_x_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec_ref(v_x_3342_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v_as_3352_, size_t v_sz_3353_, size_t v_i_3354_, lean_object* v_b_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_usize_dec_lt(v_i_3354_, v_sz_3353_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_b_3355_);
return v___x_3362_;
}
else
{
lean_object* v_snd_3363_; lean_object* v_fst_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3461_; 
v_snd_3363_ = lean_ctor_get(v_b_3355_, 1);
v_fst_3364_ = lean_ctor_get(v_b_3355_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v_b_3355_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3366_ = v_b_3355_;
v_isShared_3367_ = v_isSharedCheck_3461_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3364_);
lean_dec(v_b_3355_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3461_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3460_; 
v_fst_3368_ = lean_ctor_get(v_snd_3363_, 0);
v_snd_3369_ = lean_ctor_get(v_snd_3363_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_snd_3363_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3371_ = v_snd_3363_;
v_isShared_3372_ = v_isSharedCheck_3460_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3369_);
lean_inc(v_fst_3368_);
lean_dec(v_snd_3363_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3460_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_next_3381_; 
v_next_3381_ = lean_ctor_get(v_snd_3369_, 0);
lean_inc(v_next_3381_);
if (lean_obj_tag(v_next_3381_) == 0)
{
goto v___jp_3373_;
}
else
{
lean_object* v_upperBound_3382_; lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3459_; 
v_upperBound_3382_ = lean_ctor_get(v_snd_3369_, 1);
v_val_3383_ = lean_ctor_get(v_next_3381_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_next_3381_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3385_ = v_next_3381_;
v_isShared_3386_ = v_isSharedCheck_3459_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v_next_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3459_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_nat_dec_lt(v_val_3383_, v_upperBound_3382_);
if (v___x_3387_ == 0)
{
lean_del_object(v___x_3385_);
lean_dec(v_val_3383_);
goto v___jp_3373_;
}
else
{
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3456_; 
lean_inc(v_upperBound_3382_);
lean_del_object(v___x_3371_);
lean_del_object(v___x_3366_);
v_isSharedCheck_3456_ = !lean_is_exclusive(v_snd_3369_);
if (v_isSharedCheck_3456_ == 0)
{
lean_object* v_unused_3457_; lean_object* v_unused_3458_; 
v_unused_3457_ = lean_ctor_get(v_snd_3369_, 1);
lean_dec(v_unused_3457_);
v_unused_3458_ = lean_ctor_get(v_snd_3369_, 0);
lean_dec(v_unused_3458_);
v___x_3389_ = v_snd_3369_;
v_isShared_3390_ = v_isSharedCheck_3456_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v_snd_3369_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3456_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v_array_3391_; lean_object* v_start_3392_; lean_object* v_stop_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v_array_3391_ = lean_ctor_get(v_fst_3368_, 0);
v_start_3392_ = lean_ctor_get(v_fst_3368_, 1);
v_stop_3393_ = lean_ctor_get(v_fst_3368_, 2);
v___x_3394_ = lean_unsigned_to_nat(1u);
v___x_3395_ = lean_nat_add(v_val_3383_, v___x_3394_);
lean_dec(v_val_3383_);
lean_inc(v___x_3395_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3395_);
v___x_3397_ = v___x_3385_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3399_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3397_);
v___x_3399_ = v___x_3389_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_upperBound_3382_);
v___x_3399_ = v_reuseFailAlloc_3454_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_nat_dec_lt(v_start_3392_, v_stop_3393_);
if (v___x_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v___x_3395_);
v___x_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3401_, 0, v_fst_3368_);
lean_ctor_set(v___x_3401_, 1, v___x_3399_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v_fst_3364_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
return v___x_3403_;
}
else
{
lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3450_; 
lean_inc(v_stop_3393_);
lean_inc(v_start_3392_);
lean_inc_ref(v_array_3391_);
v_isSharedCheck_3450_ = !lean_is_exclusive(v_fst_3368_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; lean_object* v_unused_3452_; lean_object* v_unused_3453_; 
v_unused_3451_ = lean_ctor_get(v_fst_3368_, 2);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_fst_3368_, 1);
lean_dec(v_unused_3452_);
v_unused_3453_ = lean_ctor_get(v_fst_3368_, 0);
lean_dec(v_unused_3453_);
v___x_3405_ = v_fst_3368_;
v_isShared_3406_ = v_isSharedCheck_3450_;
goto v_resetjp_3404_;
}
else
{
lean_dec(v_fst_3368_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3450_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
uint8_t v___x_3407_; lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3407_ = lean_nat_dec_lt(v___x_3350_, v___x_3351_);
v_a_3408_ = lean_array_uget_borrowed(v_as_3352_, v_i_3354_);
v___x_3409_ = lean_array_fget_borrowed(v_array_3391_, v_start_3392_);
v___x_3410_ = lean_box(v___x_3407_);
lean_inc(v___x_3409_);
lean_inc(v_a_3408_);
v___f_3411_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3411_, 0, v_a_3408_);
lean_closure_set(v___f_3411_, 1, v___x_3410_);
lean_closure_set(v___f_3411_, 2, v___x_3409_);
v___x_3412_ = lean_nat_add(v_start_3392_, v___x_3394_);
lean_dec(v_start_3392_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3412_);
v___x_3414_ = v___x_3405_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_array_3391_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_stop_3393_);
v___x_3414_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; 
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v_a_3408_);
v___x_3415_ = lean_infer_type(v_a_3408_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = 0;
v___x_3418_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3416_, v___f_3411_, v___x_3417_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; size_t v___x_3430_; size_t v___x_3431_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v___f_3420_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3420_, 0, v_a_3419_);
v___x_3421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3422_ = l_Nat_reprFast(v___x_3395_);
v___x_3423_ = lean_string_append(v___x_3421_, v___x_3422_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_Name_str___override(v___x_3424_, v___x_3423_);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___f_3420_);
v___x_3427_ = lean_array_push(v_fst_3364_, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3414_);
lean_ctor_set(v___x_3428_, 1, v___x_3399_);
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = ((size_t)1ULL);
v___x_3431_ = lean_usize_add(v_i_3354_, v___x_3430_);
v_i_3354_ = v___x_3431_;
v_b_3355_ = v___x_3429_;
goto _start;
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_dec_ref(v___x_3414_);
lean_dec_ref(v___x_3399_);
lean_dec(v___x_3395_);
lean_dec(v_fst_3364_);
v_a_3433_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3418_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3418_);
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
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3448_; 
lean_dec_ref(v___x_3414_);
lean_dec_ref(v___f_3411_);
lean_dec_ref(v___x_3399_);
lean_dec(v___x_3395_);
lean_dec(v_fst_3364_);
v_a_3441_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3415_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3415_);
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
}
}
}
}
}
}
}
v___jp_3373_:
{
lean_object* v___x_3375_; 
if (v_isShared_3372_ == 0)
{
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_fst_3368_);
lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_snd_3369_);
v___x_3375_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3375_);
v___x_3377_ = v___x_3366_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_fst_3364_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3462_, lean_object* v___x_3463_, lean_object* v_as_3464_, lean_object* v_sz_3465_, lean_object* v_i_3466_, lean_object* v_b_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
size_t v_sz_boxed_3473_; size_t v_i_boxed_3474_; lean_object* v_res_3475_; 
v_sz_boxed_3473_ = lean_unbox_usize(v_sz_3465_);
lean_dec(v_sz_3465_);
v_i_boxed_3474_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3462_, v___x_3463_, v_as_3464_, v_sz_boxed_3473_, v_i_boxed_3474_, v_b_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec_ref(v_as_3464_);
lean_dec(v___x_3463_);
lean_dec(v___x_3462_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3476_, size_t v_i_3477_, lean_object* v_bs_3478_){
_start:
{
uint8_t v___x_3479_; 
v___x_3479_ = lean_usize_dec_lt(v_i_3477_, v_sz_3476_);
if (v___x_3479_ == 0)
{
return v_bs_3478_;
}
else
{
lean_object* v_v_3480_; lean_object* v_fst_3481_; lean_object* v_snd_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3498_; 
v_v_3480_ = lean_array_uget(v_bs_3478_, v_i_3477_);
v_fst_3481_ = lean_ctor_get(v_v_3480_, 0);
v_snd_3482_ = lean_ctor_get(v_v_3480_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_v_3480_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3484_ = v_v_3480_;
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snd_3482_);
lean_inc(v_fst_3481_);
lean_dec(v_v_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v_bs_x27_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3486_ = lean_unsigned_to_nat(0u);
v_bs_x27_3487_ = lean_array_uset(v_bs_3478_, v_i_3477_, v___x_3486_);
v___x_3488_ = 0;
v___x_3489_ = lean_box(v___x_3488_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3489_);
v___x_3491_ = v___x_3484_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_snd_3482_);
v___x_3491_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3492_, 0, v_fst_3481_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3477_, v___x_3493_);
v___x_3495_ = lean_array_uset(v_bs_x27_3487_, v_i_3477_, v___x_3492_);
v_i_3477_ = v___x_3494_;
v_bs_3478_ = v___x_3495_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3499_, lean_object* v_i_3500_, lean_object* v_bs_3501_){
_start:
{
size_t v_sz_boxed_3502_; size_t v_i_boxed_3503_; lean_object* v_res_3504_; 
v_sz_boxed_3502_ = lean_unbox_usize(v_sz_3499_);
lean_dec(v_sz_3499_);
v_i_boxed_3503_ = lean_unbox_usize(v_i_3500_);
lean_dec(v_i_3500_);
v_res_3504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3502_, v_i_boxed_3503_, v_bs_3501_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v_a_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_33088__overap_3513_; lean_object* v___x_3514_; 
v___x_33088__overap_3513_ = l_instInhabitedOfMonad___redArg(v___x_3505_, v___x_3506_);
lean_inc(v___y_3511_);
lean_inc_ref(v___y_3510_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
v___x_3514_ = lean_apply_5(v___x_33088__overap_3513_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, lean_box(0));
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3515_, lean_object* v___x_3516_, lean_object* v_a_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3515_, v___x_3516_, v_a_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_instMonadEIO___redArg();
return v___x_3524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3526_ = l_StateRefT_x27_instMonad___redArg(v___x_3525_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3531_, lean_object* v_declInfos_3532_, lean_object* v_k_3533_, lean_object* v_kind_3534_, lean_object* v_b_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
uint8_t v_kind_boxed_3541_; lean_object* v_res_3542_; 
v_kind_boxed_3541_ = lean_unbox(v_kind_3534_);
v_res_3542_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3531_, v_declInfos_3532_, v_k_3533_, v_kind_boxed_3541_, v_b_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3543_, lean_object* v_declInfos_3544_, lean_object* v_k_3545_, uint8_t v_kind_3546_, lean_object* v_name_3547_, uint8_t v_bi_3548_, lean_object* v_type_3549_, uint8_t v_kind_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; 
v___x_3556_ = lean_box(v_kind_3546_);
v___f_3557_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3557_, 0, v_acc_3543_);
lean_closure_set(v___f_3557_, 1, v_declInfos_3544_);
lean_closure_set(v___f_3557_, 2, v_k_3545_);
lean_closure_set(v___f_3557_, 3, v___x_3556_);
v___x_3558_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3547_, v_bi_3548_, v_type_3549_, v___f_3557_, v_kind_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
v_a_3567_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3558_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3558_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3575_, lean_object* v_k_3576_, uint8_t v_kind_3577_, lean_object* v_acc_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_){
_start:
{
lean_object* v___x_3584_; lean_object* v_toApplicative_3585_; lean_object* v_toFunctor_3586_; lean_object* v_toSeq_3587_; lean_object* v_toSeqLeft_3588_; lean_object* v_toSeqRight_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___f_3595_; lean_object* v___f_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_toApplicative_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3657_; 
v___x_3584_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3585_ = lean_ctor_get(v___x_3584_, 0);
v_toFunctor_3586_ = lean_ctor_get(v_toApplicative_3585_, 0);
v_toSeq_3587_ = lean_ctor_get(v_toApplicative_3585_, 2);
v_toSeqLeft_3588_ = lean_ctor_get(v_toApplicative_3585_, 3);
v_toSeqRight_3589_ = lean_ctor_get(v_toApplicative_3585_, 4);
v___f_3590_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3591_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3586_, 2);
v___f_3592_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3592_, 0, v_toFunctor_3586_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toFunctor_3586_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___f_3592_);
lean_ctor_set(v___x_3594_, 1, v___f_3593_);
lean_inc(v_toSeqRight_3589_);
v___f_3595_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3595_, 0, v_toSeqRight_3589_);
lean_inc(v_toSeqLeft_3588_);
v___f_3596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3596_, 0, v_toSeqLeft_3588_);
lean_inc(v_toSeq_3587_);
v___f_3597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3597_, 0, v_toSeq_3587_);
v___x_3598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3594_);
lean_ctor_set(v___x_3598_, 1, v___f_3590_);
lean_ctor_set(v___x_3598_, 2, v___f_3597_);
lean_ctor_set(v___x_3598_, 3, v___f_3596_);
lean_ctor_set(v___x_3598_, 4, v___f_3595_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v___f_3591_);
v___x_3600_ = l_StateRefT_x27_instMonad___redArg(v___x_3599_);
v_toApplicative_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; 
v_unused_3658_ = lean_ctor_get(v___x_3600_, 1);
lean_dec(v_unused_3658_);
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3657_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_toApplicative_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3657_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_toFunctor_3605_; lean_object* v_toSeq_3606_; lean_object* v_toSeqLeft_3607_; lean_object* v_toSeqRight_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3655_; 
v_toFunctor_3605_ = lean_ctor_get(v_toApplicative_3601_, 0);
v_toSeq_3606_ = lean_ctor_get(v_toApplicative_3601_, 2);
v_toSeqLeft_3607_ = lean_ctor_get(v_toApplicative_3601_, 3);
v_toSeqRight_3608_ = lean_ctor_get(v_toApplicative_3601_, 4);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_toApplicative_3601_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v_toApplicative_3601_, 1);
lean_dec(v_unused_3656_);
v___x_3610_ = v_toApplicative_3601_;
v_isShared_3611_ = v_isSharedCheck_3655_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_toSeqRight_3608_);
lean_inc(v_toSeqLeft_3607_);
lean_inc(v_toSeq_3606_);
lean_inc(v_toFunctor_3605_);
lean_dec(v_toApplicative_3601_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3655_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___f_3612_; lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___f_3619_; lean_object* v___x_3621_; 
v___f_3612_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3613_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3605_);
v___f_3614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3614_, 0, v_toFunctor_3605_);
v___f_3615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3615_, 0, v_toFunctor_3605_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___f_3614_);
lean_ctor_set(v___x_3616_, 1, v___f_3615_);
v___f_3617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3617_, 0, v_toSeqRight_3608_);
v___f_3618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3618_, 0, v_toSeqLeft_3607_);
v___f_3619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3619_, 0, v_toSeq_3606_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 4, v___f_3617_);
lean_ctor_set(v___x_3610_, 3, v___f_3618_);
lean_ctor_set(v___x_3610_, 2, v___f_3619_);
lean_ctor_set(v___x_3610_, 1, v___f_3612_);
lean_ctor_set(v___x_3610_, 0, v___x_3616_);
v___x_3621_ = v___x_3610_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___f_3612_);
lean_ctor_set(v_reuseFailAlloc_3654_, 2, v___f_3619_);
lean_ctor_set(v_reuseFailAlloc_3654_, 3, v___f_3618_);
lean_ctor_set(v_reuseFailAlloc_3654_, 4, v___f_3617_);
v___x_3621_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3623_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v___f_3613_);
lean_ctor_set(v___x_3603_, 0, v___x_3621_);
v___x_3623_ = v___x_3603_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___f_3613_);
v___x_3623_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v___x_3624_ = lean_array_get_size(v_acc_3578_);
v___x_3625_ = lean_array_get_size(v_declInfos_3575_);
v___x_3626_ = lean_nat_dec_lt(v___x_3624_, v___x_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref(v___x_3623_);
lean_dec_ref(v_declInfos_3575_);
lean_inc(v___y_3582_);
lean_inc_ref(v___y_3581_);
lean_inc(v___y_3580_);
lean_inc_ref(v___y_3579_);
v___x_3627_ = lean_apply_6(v_k_3576_, v_acc_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, lean_box(0));
return v___x_3627_;
}
else
{
lean_object* v___x_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; lean_object* v___f_3631_; lean_object* v___f_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v_snd_3637_; lean_object* v_fst_3638_; lean_object* v_fst_3639_; lean_object* v_snd_3640_; lean_object* v___x_3641_; 
v___x_3628_ = lean_box(0);
v___x_3629_ = 0;
v___x_3630_ = l_Lean_instInhabitedExpr;
v___f_3631_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3631_, 0, v___x_3623_);
lean_closure_set(v___f_3631_, 1, v___x_3630_);
v___f_3632_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3632_, 0, v___f_3631_);
v___x_3633_ = lean_box(v___x_3629_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v___f_3632_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3628_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = lean_array_get(v___x_3635_, v_declInfos_3575_, v___x_3624_);
lean_dec_ref_known(v___x_3635_, 2);
v_snd_3637_ = lean_ctor_get(v___x_3636_, 1);
lean_inc(v_snd_3637_);
v_fst_3638_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_fst_3638_);
lean_dec(v___x_3636_);
v_fst_3639_ = lean_ctor_get(v_snd_3637_, 0);
lean_inc(v_fst_3639_);
v_snd_3640_ = lean_ctor_get(v_snd_3637_, 1);
lean_inc(v_snd_3640_);
lean_dec(v_snd_3637_);
lean_inc(v___y_3582_);
lean_inc_ref(v___y_3581_);
lean_inc(v___y_3580_);
lean_inc_ref(v___y_3579_);
lean_inc_ref(v_acc_3578_);
v___x_3641_ = lean_apply_6(v_snd_3640_, v_acc_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, lean_box(0));
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = lean_unbox(v_fst_3639_);
lean_dec(v_fst_3639_);
v___x_3644_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3578_, v_declInfos_3575_, v_k_3576_, v_kind_3577_, v_fst_3638_, v___x_3643_, v_a_3642_, v_kind_3577_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
return v___x_3644_;
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v_fst_3639_);
lean_dec(v_fst_3638_);
lean_dec_ref(v_acc_3578_);
lean_dec_ref(v_k_3576_);
lean_dec_ref(v_declInfos_3575_);
v_a_3645_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3641_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3641_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
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
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3659_, lean_object* v_declInfos_3660_, lean_object* v_k_3661_, uint8_t v_kind_3662_, lean_object* v_b_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_array_push(v_acc_3659_, v_b_3663_);
v___x_3670_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3660_, v_k_3661_, v_kind_3662_, v___x_3669_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3671_, lean_object* v_declInfos_3672_, lean_object* v_k_3673_, lean_object* v_kind_3674_, lean_object* v_name_3675_, lean_object* v_bi_3676_, lean_object* v_type_3677_, lean_object* v_kind_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
uint8_t v_kind_boxed_3684_; uint8_t v_bi_boxed_3685_; uint8_t v_kind_boxed_3686_; lean_object* v_res_3687_; 
v_kind_boxed_3684_ = lean_unbox(v_kind_3674_);
v_bi_boxed_3685_ = lean_unbox(v_bi_3676_);
v_kind_boxed_3686_ = lean_unbox(v_kind_3678_);
v_res_3687_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3671_, v_declInfos_3672_, v_k_3673_, v_kind_boxed_3684_, v_name_3675_, v_bi_boxed_3685_, v_type_3677_, v_kind_boxed_3686_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3688_, lean_object* v_k_3689_, lean_object* v_kind_3690_, lean_object* v_acc_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
uint8_t v_kind_boxed_3697_; lean_object* v_res_3698_; 
v_kind_boxed_3697_ = lean_unbox(v_kind_3690_);
v_res_3698_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3688_, v_k_3689_, v_kind_boxed_3697_, v_acc_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3699_, lean_object* v_k_3700_, uint8_t v_kind_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3699_, v_k_3700_, v_kind_3701_, v___x_3707_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3709_, lean_object* v_k_3710_, lean_object* v_kind_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v_kind_boxed_3717_; lean_object* v_res_3718_; 
v_kind_boxed_3717_ = lean_unbox(v_kind_3711_);
v_res_3718_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3709_, v_k_3710_, v_kind_boxed_3717_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3719_, lean_object* v_k_3720_, uint8_t v_kind_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_sz_3727_ = lean_array_size(v_declInfos_3719_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3727_, v___x_3728_, v_declInfos_3719_);
v___x_3730_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3729_, v_k_3720_, v_kind_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3731_, lean_object* v_k_3732_, lean_object* v_kind_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
uint8_t v_kind_boxed_3739_; lean_object* v_res_3740_; 
v_kind_boxed_3739_ = lean_unbox(v_kind_3733_);
v_res_3740_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3731_, v_k_3732_, v_kind_boxed_3739_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
return v_res_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3743_ = lean_unsigned_to_nat(4u);
v___x_3744_ = lean_unsigned_to_nat(202u);
v___x_3745_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3746_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3747_ = l_mkPanicMessageWithDecl(v___x_3746_, v___x_3745_, v___x_3744_, v___x_3743_, v___x_3742_);
return v___x_3747_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3754_ = l_Lean_stringToMessageData(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3757_ = l_Lean_stringToMessageData(v___x_3756_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3758_, lean_object* v_numMotives_3759_, lean_object* v_numMinors_3760_, lean_object* v___x_3761_, lean_object* v_all_3762_, lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v_head_3765_, lean_object* v_tail_3766_, lean_object* v_recName_3767_, lean_object* v_brecOnGoName_3768_, lean_object* v_levelParams_3769_, lean_object* v_brecOnName_3770_, lean_object* v_brecOnEqName_3771_, lean_object* v_type_3772_, lean_object* v_refArgs_3773_, lean_object* v_refBody_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3780_ = lean_nat_add(v_nParams_3758_, v_numMotives_3759_);
v___x_3781_ = lean_nat_add(v___x_3780_, v_numMinors_3760_);
v___x_3782_ = lean_array_get_size(v_refArgs_3773_);
v___x_3783_ = lean_nat_dec_lt(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
lean_dec(v___x_3781_);
lean_dec(v___x_3780_);
lean_dec_ref(v_refArgs_3773_);
lean_dec_ref(v_type_3772_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3763_);
lean_dec_ref(v_all_3762_);
lean_dec(v___x_3761_);
lean_dec(v_nParams_3758_);
v___x_3784_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3785_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3784_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3785_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3786_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3758_);
lean_inc_ref_n(v_refArgs_3773_, 2);
v___x_3787_ = l_Array_toSubarray___redArg(v_refArgs_3773_, v___x_3786_, v_nParams_3758_);
lean_inc(v___x_3780_);
v___x_3788_ = l_Array_toSubarray___redArg(v_refArgs_3773_, v_nParams_3758_, v___x_3780_);
v___x_3789_ = l_Subarray_copy___redArg(v___x_3788_);
v___x_3790_ = l_Lean_Expr_getAppFn(v_refBody_3774_);
v___x_3791_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3789_, v___x_3790_);
lean_dec_ref(v___x_3790_);
if (lean_obj_tag(v___x_3791_) == 1)
{
lean_object* v_val_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___f_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec_ref(v_type_3772_);
v_val_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_val_3792_);
lean_dec_ref_known(v___x_3791_, 1);
lean_inc_n(v___x_3781_, 2);
lean_inc_ref_n(v_refArgs_3773_, 2);
v___x_3793_ = l_Array_toSubarray___redArg(v_refArgs_3773_, v___x_3780_, v___x_3781_);
v___x_3794_ = l_Subarray_copy___redArg(v___x_3787_);
v___x_3795_ = l_Subarray_copy___redArg(v___x_3793_);
v___x_3796_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3789_);
lean_inc_ref(v___x_3794_);
lean_inc(v___x_3761_);
v___f_3797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3797_, 0, v___x_3761_);
lean_closure_set(v___f_3797_, 1, v___x_3794_);
lean_closure_set(v___f_3797_, 2, v___x_3789_);
lean_closure_set(v___f_3797_, 3, v_all_3762_);
lean_closure_set(v___f_3797_, 4, v___x_3763_);
lean_closure_set(v___f_3797_, 5, v___x_3786_);
lean_closure_set(v___f_3797_, 6, v___x_3796_);
v___x_3798_ = lean_nat_sub(v___x_3782_, v___x_3796_);
lean_inc(v___x_3798_);
v___x_3799_ = l_Array_toSubarray___redArg(v_refArgs_3773_, v___x_3781_, v___x_3798_);
v___x_3800_ = l_Subarray_copy___redArg(v___x_3799_);
v___x_3801_ = lean_array_get(v___x_3764_, v_refArgs_3773_, v___x_3798_);
lean_dec(v___x_3798_);
lean_dec_ref(v_refArgs_3773_);
lean_inc(v___y_3778_);
lean_inc_ref(v___y_3777_);
lean_inc(v___y_3776_);
lean_inc_ref(v___y_3775_);
lean_inc(v___x_3801_);
v___x_3802_ = lean_infer_type(v___x_3801_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
lean_inc(v___y_3778_);
lean_inc_ref(v___y_3777_);
lean_inc(v___y_3776_);
lean_inc_ref(v___y_3775_);
v___x_3804_ = lean_infer_type(v_a_3803_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___x_3806_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3805_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
if (lean_obj_tag(v_a_3807_) == 1)
{
lean_object* v_val_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___f_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; size_t v_sz_3821_; size_t v___x_3822_; lean_object* v___x_3823_; 
v_val_3808_ = lean_ctor_get(v_a_3807_, 0);
lean_inc(v_val_3808_);
lean_dec_ref_known(v_a_3807_, 1);
v___x_3809_ = l_Lean_mkLevelMax(v_val_3808_, v_head_3765_);
v___x_3810_ = lean_array_get_size(v___x_3789_);
v___x_3811_ = l_Array_ofFn___redArg(v___x_3810_, v___f_3797_);
v___x_3812_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3813_ = lean_array_get_size(v___x_3811_);
lean_inc_ref(v___x_3811_);
v___x_3814_ = l_Array_toSubarray___redArg(v___x_3811_, v___x_3786_, v___x_3813_);
v___x_3815_ = lean_box(v___x_3783_);
lean_inc(v___x_3781_);
lean_inc_ref(v___x_3789_);
lean_inc_ref(v___x_3814_);
v___f_3816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3816_, 0, v___x_3809_);
lean_closure_set(v___f_3816_, 1, v_tail_3766_);
lean_closure_set(v___f_3816_, 2, v_recName_3767_);
lean_closure_set(v___f_3816_, 3, v___x_3794_);
lean_closure_set(v___f_3816_, 4, v___x_3814_);
lean_closure_set(v___f_3816_, 5, v___x_3789_);
lean_closure_set(v___f_3816_, 6, v___x_3781_);
lean_closure_set(v___f_3816_, 7, v___x_3782_);
lean_closure_set(v___f_3816_, 8, v___x_3795_);
lean_closure_set(v___f_3816_, 9, v___x_3811_);
lean_closure_set(v___f_3816_, 10, v___x_3800_);
lean_closure_set(v___f_3816_, 11, v___x_3801_);
lean_closure_set(v___f_3816_, 12, v___x_3796_);
lean_closure_set(v___f_3816_, 13, v___x_3764_);
lean_closure_set(v___f_3816_, 14, v_val_3792_);
lean_closure_set(v___f_3816_, 15, v___x_3815_);
lean_closure_set(v___f_3816_, 16, v_brecOnGoName_3768_);
lean_closure_set(v___f_3816_, 17, v_levelParams_3769_);
lean_closure_set(v___f_3816_, 18, v___x_3786_);
lean_closure_set(v___f_3816_, 19, v___x_3761_);
lean_closure_set(v___f_3816_, 20, v_brecOnName_3770_);
lean_closure_set(v___f_3816_, 21, v_brecOnEqName_3771_);
v___x_3817_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v___x_3810_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3814_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3812_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v_sz_3821_ = lean_array_size(v___x_3789_);
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3781_, v___x_3782_, v___x_3789_, v_sz_3821_, v___x_3822_, v___x_3820_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3781_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v_fst_3825_; uint8_t v___x_3826_; lean_object* v___x_3827_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v_fst_3825_ = lean_ctor_get(v_a_3824_, 0);
lean_inc(v_fst_3825_);
lean_dec(v_a_3824_);
v___x_3826_ = 0;
v___x_3827_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3825_, v___f_3816_, v___x_3826_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v___f_3816_);
v_a_3828_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3823_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3823_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_a_3807_);
lean_dec_ref(v___x_3800_);
lean_dec_ref(v___f_3797_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3794_);
lean_dec(v_val_3792_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3781_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3761_);
v___x_3836_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3837_ = l_Lean_MessageData_ofExpr(v___x_3801_);
v___x_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3840_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3841_;
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v___x_3801_);
lean_dec_ref(v___x_3800_);
lean_dec_ref(v___f_3797_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3794_);
lean_dec(v_val_3792_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3781_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3761_);
v_a_3842_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3806_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3806_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec(v___x_3801_);
lean_dec_ref(v___x_3800_);
lean_dec_ref(v___f_3797_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3794_);
lean_dec(v_val_3792_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3781_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3761_);
v_a_3850_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3804_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3804_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v___x_3801_);
lean_dec_ref(v___x_3800_);
lean_dec_ref(v___f_3797_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3794_);
lean_dec(v_val_3792_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3781_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3761_);
v_a_3858_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3802_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3802_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v___x_3791_);
lean_dec_ref(v___x_3787_);
lean_dec(v___x_3781_);
lean_dec(v___x_3780_);
lean_dec_ref(v_refArgs_3773_);
lean_dec(v_brecOnEqName_3771_);
lean_dec(v_brecOnName_3770_);
lean_dec(v_levelParams_3769_);
lean_dec(v_brecOnGoName_3768_);
lean_dec(v_recName_3767_);
lean_dec(v_tail_3766_);
lean_dec(v_head_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3763_);
lean_dec_ref(v_all_3762_);
lean_dec(v___x_3761_);
v___x_3866_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3867_ = l_Lean_MessageData_ofExpr(v_type_3772_);
v___x_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3868_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = lean_array_to_list(v___x_3789_);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3871_, v___x_3872_);
v___x_3874_ = l_Lean_MessageData_ofList(v___x_3873_);
v___x_3875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3870_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3875_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
return v___x_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3877_ = _args[0];
lean_object* v_numMotives_3878_ = _args[1];
lean_object* v_numMinors_3879_ = _args[2];
lean_object* v___x_3880_ = _args[3];
lean_object* v_all_3881_ = _args[4];
lean_object* v___x_3882_ = _args[5];
lean_object* v___x_3883_ = _args[6];
lean_object* v_head_3884_ = _args[7];
lean_object* v_tail_3885_ = _args[8];
lean_object* v_recName_3886_ = _args[9];
lean_object* v_brecOnGoName_3887_ = _args[10];
lean_object* v_levelParams_3888_ = _args[11];
lean_object* v_brecOnName_3889_ = _args[12];
lean_object* v_brecOnEqName_3890_ = _args[13];
lean_object* v_type_3891_ = _args[14];
lean_object* v_refArgs_3892_ = _args[15];
lean_object* v_refBody_3893_ = _args[16];
lean_object* v___y_3894_ = _args[17];
lean_object* v___y_3895_ = _args[18];
lean_object* v___y_3896_ = _args[19];
lean_object* v___y_3897_ = _args[20];
lean_object* v___y_3898_ = _args[21];
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3877_, v_numMotives_3878_, v_numMinors_3879_, v___x_3880_, v_all_3881_, v___x_3882_, v___x_3883_, v_head_3884_, v_tail_3885_, v_recName_3886_, v_brecOnGoName_3887_, v_levelParams_3888_, v_brecOnName_3889_, v_brecOnEqName_3890_, v_type_3891_, v_refArgs_3892_, v_refBody_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_refBody_3893_);
lean_dec(v_numMinors_3879_);
lean_dec(v_numMotives_3878_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3902_, lean_object* v_nParams_3903_, lean_object* v_all_3904_, lean_object* v_brecOnName_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v_brecOnGoName_3914_; lean_object* v___x_3915_; lean_object* v_brecOnEqName_3916_; lean_object* v___x_3917_; 
v___x_3911_ = l_Lean_instInhabitedExpr;
v___x_3912_ = lean_box(0);
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3905_, 2);
v_brecOnGoName_3914_ = l_Lean_Name_str___override(v_brecOnName_3905_, v___x_3913_);
v___x_3915_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3916_ = l_Lean_Name_str___override(v_brecOnName_3905_, v___x_3915_);
lean_inc(v_recName_3902_);
v___x_3917_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3902_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3945_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3920_ = v___x_3917_;
v_isShared_3921_ = v_isSharedCheck_3945_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3917_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3945_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
if (lean_obj_tag(v_a_3918_) == 7)
{
lean_object* v_val_3922_; lean_object* v_toConstantVal_3923_; lean_object* v_numMotives_3924_; lean_object* v_numMinors_3925_; lean_object* v_levelParams_3926_; lean_object* v_type_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_del_object(v___x_3920_);
v_val_3922_ = lean_ctor_get(v_a_3918_, 0);
lean_inc_ref(v_val_3922_);
lean_dec_ref_known(v_a_3918_, 1);
v_toConstantVal_3923_ = lean_ctor_get(v_val_3922_, 0);
lean_inc_ref(v_toConstantVal_3923_);
v_numMotives_3924_ = lean_ctor_get(v_val_3922_, 4);
lean_inc(v_numMotives_3924_);
v_numMinors_3925_ = lean_ctor_get(v_val_3922_, 5);
lean_inc(v_numMinors_3925_);
lean_dec_ref(v_val_3922_);
v_levelParams_3926_ = lean_ctor_get(v_toConstantVal_3923_, 1);
lean_inc_n(v_levelParams_3926_, 2);
v_type_3927_ = lean_ctor_get(v_toConstantVal_3923_, 2);
lean_inc_ref(v_type_3927_);
lean_dec_ref(v_toConstantVal_3923_);
v___x_3928_ = lean_box(0);
v___x_3929_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3926_, v___x_3928_);
if (lean_obj_tag(v___x_3929_) == 1)
{
lean_object* v_head_3930_; lean_object* v_tail_3931_; lean_object* v___f_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; 
v_head_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_head_3930_);
v_tail_3931_ = lean_ctor_get(v___x_3929_, 1);
lean_inc(v_tail_3931_);
lean_inc_ref(v_type_3927_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3932_, 0, v_nParams_3903_);
lean_closure_set(v___f_3932_, 1, v_numMotives_3924_);
lean_closure_set(v___f_3932_, 2, v_numMinors_3925_);
lean_closure_set(v___f_3932_, 3, v___x_3929_);
lean_closure_set(v___f_3932_, 4, v_all_3904_);
lean_closure_set(v___f_3932_, 5, v___x_3912_);
lean_closure_set(v___f_3932_, 6, v___x_3911_);
lean_closure_set(v___f_3932_, 7, v_head_3930_);
lean_closure_set(v___f_3932_, 8, v_tail_3931_);
lean_closure_set(v___f_3932_, 9, v_recName_3902_);
lean_closure_set(v___f_3932_, 10, v_brecOnGoName_3914_);
lean_closure_set(v___f_3932_, 11, v_levelParams_3926_);
lean_closure_set(v___f_3932_, 12, v_brecOnName_3905_);
lean_closure_set(v___f_3932_, 13, v_brecOnEqName_3916_);
lean_closure_set(v___f_3932_, 14, v_type_3927_);
v___x_3933_ = 0;
v___x_3934_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3927_, v___f_3932_, v___x_3933_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
return v___x_3934_;
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v___x_3929_);
lean_dec_ref(v_type_3927_);
lean_dec(v_levelParams_3926_);
lean_dec(v_numMinors_3925_);
lean_dec(v_numMotives_3924_);
lean_dec(v_brecOnEqName_3916_);
lean_dec(v_brecOnGoName_3914_);
lean_dec(v_brecOnName_3905_);
lean_dec_ref(v_all_3904_);
lean_dec(v_nParams_3903_);
v___x_3935_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3936_ = l_Lean_MessageData_ofName(v_recName_3902_);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3935_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3939_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
return v___x_3940_;
}
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
lean_dec(v_a_3918_);
lean_dec(v_brecOnEqName_3916_);
lean_dec(v_brecOnGoName_3914_);
lean_dec(v_brecOnName_3905_);
lean_dec_ref(v_all_3904_);
lean_dec(v_nParams_3903_);
lean_dec(v_recName_3902_);
v___x_3941_ = lean_box(0);
if (v_isShared_3921_ == 0)
{
lean_ctor_set(v___x_3920_, 0, v___x_3941_);
v___x_3943_ = v___x_3920_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_brecOnEqName_3916_);
lean_dec(v_brecOnGoName_3914_);
lean_dec(v_brecOnName_3905_);
lean_dec_ref(v_all_3904_);
lean_dec(v_nParams_3903_);
lean_dec(v_recName_3902_);
v_a_3946_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3917_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3917_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3954_, lean_object* v_nParams_3955_, lean_object* v_all_3956_, lean_object* v_brecOnName_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3954_, v_nParams_3955_, v_all_3956_, v_brecOnName_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3964_, lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v_a_3969_, lean_object* v_b_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_){
_start:
{
uint8_t v___x_3976_; 
v___x_3976_ = lean_nat_dec_lt(v_a_3969_, v_upperBound_3964_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_dec(v_a_3969_);
lean_dec_ref(v___x_3968_);
lean_dec(v___x_3967_);
lean_dec(v___x_3966_);
lean_dec(v___x_3965_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v_b_3970_);
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_unsigned_to_nat(1u);
v___x_3980_ = lean_nat_add(v_a_3969_, v___x_3979_);
lean_dec(v_a_3969_);
lean_inc_n(v___x_3980_, 2);
lean_inc(v___x_3965_);
v___x_3981_ = lean_name_append_index_after(v___x_3965_, v___x_3980_);
lean_inc(v___x_3966_);
v___x_3982_ = lean_name_append_index_after(v___x_3966_, v___x_3980_);
lean_inc_ref(v___x_3968_);
lean_inc(v___x_3967_);
v___x_3983_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3981_, v___x_3967_, v___x_3968_, v___x_3982_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_dec_ref_known(v___x_3983_, 1);
v_a_3969_ = v___x_3980_;
v_b_3970_ = v___x_3978_;
goto _start;
}
else
{
lean_dec(v___x_3980_);
lean_dec_ref(v___x_3968_);
lean_dec(v___x_3967_);
lean_dec(v___x_3966_);
lean_dec(v___x_3965_);
return v___x_3983_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3985_, lean_object* v___x_3986_, lean_object* v___x_3987_, lean_object* v___x_3988_, lean_object* v___x_3989_, lean_object* v_a_3990_, lean_object* v_b_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3985_, v___x_3986_, v___x_3987_, v___x_3988_, v___x_3989_, v_a_3990_, v_b_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v_upperBound_3985_);
return v_res_3997_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4002_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4003_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_4004_ = l_Lean_Name_append(v___x_4003_, v___x_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_toCold_4011_; lean_object* v_options_4012_; lean_object* v_inheritedTraceOptions_4013_; uint8_t v_hasTrace_4014_; lean_object* v___x_4015_; 
v_toCold_4011_ = lean_ctor_get(v_a_4008_, 0);
v_options_4012_ = lean_ctor_get(v_toCold_4011_, 2);
v_inheritedTraceOptions_4013_ = lean_ctor_get(v_toCold_4011_, 11);
v_hasTrace_4014_ = lean_ctor_get_uint8(v_options_4012_, sizeof(void*)*1);
v___x_4015_ = lean_box(0);
if (v_hasTrace_4014_ == 0)
{
lean_object* v___x_4016_; 
lean_inc(v_indName_4005_);
v___x_4016_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4081_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4019_ = v___x_4016_;
v_isShared_4020_ = v_isSharedCheck_4081_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4081_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
if (lean_obj_tag(v_a_4017_) == 5)
{
lean_object* v_val_4021_; uint8_t v_isRec_4022_; 
v_val_4021_ = lean_ctor_get(v_a_4017_, 0);
lean_inc_ref(v_val_4021_);
lean_dec_ref_known(v_a_4017_, 1);
v_isRec_4022_ = lean_ctor_get_uint8(v_val_4021_, sizeof(void*)*6);
if (v_isRec_4022_ == 0)
{
lean_object* v___x_4023_; lean_object* v___x_4025_; 
lean_dec_ref(v_val_4021_);
lean_dec(v_indName_4005_);
v___x_4023_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4023_);
v___x_4025_ = v___x_4019_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
else
{
lean_object* v_toConstantVal_4027_; lean_object* v_numParams_4028_; lean_object* v_all_4029_; lean_object* v_numNested_4030_; lean_object* v_type_4031_; lean_object* v___x_4032_; 
lean_del_object(v___x_4019_);
v_toConstantVal_4027_ = lean_ctor_get(v_val_4021_, 0);
lean_inc_ref(v_toConstantVal_4027_);
v_numParams_4028_ = lean_ctor_get(v_val_4021_, 1);
lean_inc(v_numParams_4028_);
v_all_4029_ = lean_ctor_get(v_val_4021_, 3);
lean_inc(v_all_4029_);
v_numNested_4030_ = lean_ctor_get(v_val_4021_, 5);
lean_inc(v_numNested_4030_);
lean_dec_ref(v_val_4021_);
v_type_4031_ = lean_ctor_get(v_toConstantVal_4027_, 2);
lean_inc_ref(v_type_4031_);
lean_dec_ref(v_toConstantVal_4027_);
v___x_4032_ = l_Lean_Meta_isPropFormerType(v_type_4031_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4068_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4068_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4068_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
uint8_t v___x_4037_; 
v___x_4037_ = lean_unbox(v_a_4033_);
lean_dec(v_a_4033_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_del_object(v___x_4035_);
lean_inc_n(v_indName_4005_, 2);
v___x_4038_ = l_Lean_mkRecName(v_indName_4005_);
v___x_4039_ = l_Lean_mkBRecOnName(v_indName_4005_);
lean_inc(v_all_4029_);
v___x_4040_ = lean_array_mk(v_all_4029_);
lean_inc(v___x_4039_);
lean_inc_ref(v___x_4040_);
lean_inc(v_numParams_4028_);
lean_inc(v___x_4038_);
v___x_4041_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4038_, v_numParams_4028_, v___x_4040_, v___x_4039_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4062_; 
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4062_ == 0)
{
lean_object* v_unused_4063_; 
v_unused_4063_ = lean_ctor_get(v___x_4041_, 0);
lean_dec(v_unused_4063_);
v___x_4043_ = v___x_4041_;
v_isShared_4044_ = v_isSharedCheck_4062_;
goto v_resetjp_4042_;
}
else
{
lean_dec(v___x_4041_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4062_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v___x_4045_ = lean_unsigned_to_nat(0u);
v___x_4046_ = l_List_get_x21Internal___redArg(v___x_4015_, v_all_4029_, v___x_4045_);
lean_dec(v_all_4029_);
v___x_4047_ = lean_name_eq(v___x_4046_, v_indName_4005_);
lean_dec(v_indName_4005_);
lean_dec(v___x_4046_);
if (v___x_4047_ == 0)
{
lean_object* v___x_4048_; lean_object* v___x_4050_; 
lean_dec_ref(v___x_4040_);
lean_dec(v___x_4039_);
lean_dec(v___x_4038_);
lean_dec(v_numNested_4030_);
lean_dec(v_numParams_4028_);
v___x_4048_ = lean_box(0);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v___x_4048_);
v___x_4050_ = v___x_4043_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
lean_del_object(v___x_4043_);
v___x_4052_ = lean_box(0);
v___x_4053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4030_, v___x_4038_, v___x_4039_, v_numParams_4028_, v___x_4040_, v___x_4045_, v___x_4052_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_numNested_4030_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4053_, 0);
lean_dec(v_unused_4061_);
v___x_4055_ = v___x_4053_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v___x_4053_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4052_);
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4052_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
else
{
return v___x_4053_;
}
}
}
}
else
{
lean_dec_ref(v___x_4040_);
lean_dec(v___x_4039_);
lean_dec(v___x_4038_);
lean_dec(v_numNested_4030_);
lean_dec(v_all_4029_);
lean_dec(v_numParams_4028_);
lean_dec(v_indName_4005_);
return v___x_4041_;
}
}
else
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
lean_dec(v_numNested_4030_);
lean_dec(v_all_4029_);
lean_dec(v_numParams_4028_);
lean_dec(v_indName_4005_);
v___x_4064_ = lean_box(0);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v___x_4064_);
v___x_4066_ = v___x_4035_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_numNested_4030_);
lean_dec(v_all_4029_);
lean_dec(v_numParams_4028_);
lean_dec(v_indName_4005_);
v_a_4069_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4032_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4032_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
lean_dec(v_a_4017_);
lean_dec(v_indName_4005_);
v___x_4077_ = lean_box(0);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4077_);
v___x_4079_ = v___x_4019_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec(v_indName_4005_);
v_a_4082_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4016_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4016_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
else
{
lean_object* v___f_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v_a_4098_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v_a_4113_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v_a_4118_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v_a_4123_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v_a_4135_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v_a_4140_; 
lean_inc(v_indName_4005_);
v___f_4090_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4090_, 0, v_indName_4005_);
v___x_4091_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4092_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4093_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4094_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4013_, v_options_4012_, v___x_4093_);
if (v___x_4094_ == 0)
{
lean_object* v___x_4207_; uint8_t v___x_4208_; 
v___x_4207_ = l_Lean_trace_profiler;
v___x_4208_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4012_, v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; 
lean_dec_ref(v___f_4090_);
lean_inc(v_indName_4005_);
v___x_4209_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4274_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4212_ = v___x_4209_;
v_isShared_4213_ = v_isSharedCheck_4274_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4209_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4274_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
if (lean_obj_tag(v_a_4210_) == 5)
{
lean_object* v_val_4214_; uint8_t v_isRec_4215_; 
v_val_4214_ = lean_ctor_get(v_a_4210_, 0);
lean_inc_ref(v_val_4214_);
lean_dec_ref_known(v_a_4210_, 1);
v_isRec_4215_ = lean_ctor_get_uint8(v_val_4214_, sizeof(void*)*6);
if (v_isRec_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
lean_dec_ref(v_val_4214_);
lean_dec(v_indName_4005_);
v___x_4216_ = lean_box(0);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4216_);
v___x_4218_ = v___x_4212_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
else
{
lean_object* v_toConstantVal_4220_; lean_object* v_numParams_4221_; lean_object* v_all_4222_; lean_object* v_numNested_4223_; lean_object* v_type_4224_; lean_object* v___x_4225_; 
lean_del_object(v___x_4212_);
v_toConstantVal_4220_ = lean_ctor_get(v_val_4214_, 0);
lean_inc_ref(v_toConstantVal_4220_);
v_numParams_4221_ = lean_ctor_get(v_val_4214_, 1);
lean_inc(v_numParams_4221_);
v_all_4222_ = lean_ctor_get(v_val_4214_, 3);
lean_inc(v_all_4222_);
v_numNested_4223_ = lean_ctor_get(v_val_4214_, 5);
lean_inc(v_numNested_4223_);
lean_dec_ref(v_val_4214_);
v_type_4224_ = lean_ctor_get(v_toConstantVal_4220_, 2);
lean_inc_ref(v_type_4224_);
lean_dec_ref(v_toConstantVal_4220_);
v___x_4225_ = l_Lean_Meta_isPropFormerType(v_type_4224_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4261_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4228_ = v___x_4225_;
v_isShared_4229_ = v_isSharedCheck_4261_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4261_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
uint8_t v___x_4230_; 
v___x_4230_ = lean_unbox(v_a_4226_);
lean_dec(v_a_4226_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_del_object(v___x_4228_);
lean_inc_n(v_indName_4005_, 2);
v___x_4231_ = l_Lean_mkRecName(v_indName_4005_);
v___x_4232_ = l_Lean_mkBRecOnName(v_indName_4005_);
lean_inc(v_all_4222_);
v___x_4233_ = lean_array_mk(v_all_4222_);
lean_inc(v___x_4232_);
lean_inc_ref(v___x_4233_);
lean_inc(v_numParams_4221_);
lean_inc(v___x_4231_);
v___x_4234_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4231_, v_numParams_4221_, v___x_4233_, v___x_4232_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4255_; 
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4234_);
if (v_isSharedCheck_4255_ == 0)
{
lean_object* v_unused_4256_; 
v_unused_4256_ = lean_ctor_get(v___x_4234_, 0);
lean_dec(v_unused_4256_);
v___x_4236_ = v___x_4234_;
v_isShared_4237_ = v_isSharedCheck_4255_;
goto v_resetjp_4235_;
}
else
{
lean_dec(v___x_4234_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4255_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v___x_4238_ = lean_unsigned_to_nat(0u);
v___x_4239_ = l_List_get_x21Internal___redArg(v___x_4015_, v_all_4222_, v___x_4238_);
lean_dec(v_all_4222_);
v___x_4240_ = lean_name_eq(v___x_4239_, v_indName_4005_);
lean_dec(v_indName_4005_);
lean_dec(v___x_4239_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; lean_object* v___x_4243_; 
lean_dec_ref(v___x_4233_);
lean_dec(v___x_4232_);
lean_dec(v___x_4231_);
lean_dec(v_numNested_4223_);
lean_dec(v_numParams_4221_);
v___x_4241_ = lean_box(0);
if (v_isShared_4237_ == 0)
{
lean_ctor_set(v___x_4236_, 0, v___x_4241_);
v___x_4243_ = v___x_4236_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
else
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
lean_del_object(v___x_4236_);
v___x_4245_ = lean_box(0);
v___x_4246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4223_, v___x_4231_, v___x_4232_, v_numParams_4221_, v___x_4233_, v___x_4238_, v___x_4245_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_numNested_4223_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; 
v_unused_4254_ = lean_ctor_get(v___x_4246_, 0);
lean_dec(v_unused_4254_);
v___x_4248_ = v___x_4246_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_dec(v___x_4246_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set(v___x_4248_, 0, v___x_4245_);
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4245_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
else
{
return v___x_4246_;
}
}
}
}
else
{
lean_dec_ref(v___x_4233_);
lean_dec(v___x_4232_);
lean_dec(v___x_4231_);
lean_dec(v_numNested_4223_);
lean_dec(v_all_4222_);
lean_dec(v_numParams_4221_);
lean_dec(v_indName_4005_);
return v___x_4234_;
}
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4259_; 
lean_dec(v_numNested_4223_);
lean_dec(v_all_4222_);
lean_dec(v_numParams_4221_);
lean_dec(v_indName_4005_);
v___x_4257_ = lean_box(0);
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___x_4257_);
v___x_4259_ = v___x_4228_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4260_; 
v_reuseFailAlloc_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4257_);
v___x_4259_ = v_reuseFailAlloc_4260_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
return v___x_4259_;
}
}
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec(v_numNested_4223_);
lean_dec(v_all_4222_);
lean_dec(v_numParams_4221_);
lean_dec(v_indName_4005_);
v_a_4262_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4225_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4225_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
}
else
{
lean_object* v___x_4270_; lean_object* v___x_4272_; 
lean_dec(v_a_4210_);
lean_dec(v_indName_4005_);
v___x_4270_ = lean_box(0);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4270_);
v___x_4272_ = v___x_4212_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_indName_4005_);
v_a_4275_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4209_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4209_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
goto v___jp_4142_;
}
}
else
{
goto v___jp_4142_;
}
v___jp_4095_:
{
lean_object* v___x_4099_; double v___x_4100_; double v___x_4101_; double v___x_4102_; double v___x_4103_; double v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4099_ = lean_io_mono_nanos_now();
v___x_4100_ = lean_float_of_nat(v___y_4097_);
v___x_4101_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4102_ = lean_float_div(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_float_of_nat(v___x_4099_);
v___x_4104_ = lean_float_div(v___x_4103_, v___x_4101_);
v___x_4105_ = lean_box_float(v___x_4102_);
v___x_4106_ = lean_box_float(v___x_4104_);
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4108_, 0, v_a_4098_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4091_, v_hasTrace_4014_, v___x_4092_, v_options_4012_, v___x_4094_, v___y_4096_, v___f_4090_, v___x_4108_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4109_;
}
v___jp_4110_:
{
lean_object* v___x_4114_; 
v___x_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4114_, 0, v_a_4113_);
v___y_4096_ = v___y_4111_;
v___y_4097_ = v___y_4112_;
v_a_4098_ = v___x_4114_;
goto v___jp_4095_;
}
v___jp_4115_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4118_);
v___y_4096_ = v___y_4116_;
v___y_4097_ = v___y_4117_;
v_a_4098_ = v___x_4119_;
goto v___jp_4095_;
}
v___jp_4120_:
{
lean_object* v___x_4124_; double v___x_4125_; double v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4124_ = lean_io_get_num_heartbeats();
v___x_4125_ = lean_float_of_nat(v___y_4121_);
v___x_4126_ = lean_float_of_nat(v___x_4124_);
v___x_4127_ = lean_box_float(v___x_4125_);
v___x_4128_ = lean_box_float(v___x_4126_);
v___x_4129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_a_4123_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4091_, v_hasTrace_4014_, v___x_4092_, v_options_4012_, v___x_4094_, v___y_4122_, v___f_4090_, v___x_4130_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4131_;
}
v___jp_4132_:
{
lean_object* v___x_4136_; 
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v_a_4135_);
v___y_4121_ = v___y_4133_;
v___y_4122_ = v___y_4134_;
v_a_4123_ = v___x_4136_;
goto v___jp_4120_;
}
v___jp_4137_:
{
lean_object* v___x_4141_; 
v___x_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4141_, 0, v_a_4140_);
v___y_4121_ = v___y_4138_;
v___y_4122_ = v___y_4139_;
v_a_4123_ = v___x_4141_;
goto v___jp_4120_;
}
v___jp_4142_:
{
lean_object* v___x_4143_; lean_object* v_a_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v___x_4143_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_4009_);
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref(v___x_4143_);
v___x_4145_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4146_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4012_, v___x_4145_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_io_mono_nanos_now();
lean_inc(v_indName_4005_);
v___x_4148_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
if (lean_obj_tag(v_a_4149_) == 5)
{
lean_object* v_val_4150_; uint8_t v_isRec_4151_; 
v_val_4150_ = lean_ctor_get(v_a_4149_, 0);
lean_inc_ref(v_val_4150_);
lean_dec_ref_known(v_a_4149_, 1);
v_isRec_4151_ = lean_ctor_get_uint8(v_val_4150_, sizeof(void*)*6);
if (v_isRec_4151_ == 0)
{
lean_object* v___x_4152_; 
lean_dec_ref(v_val_4150_);
lean_dec(v_indName_4005_);
v___x_4152_ = lean_box(0);
v___y_4111_ = v_a_4144_;
v___y_4112_ = v___x_4147_;
v_a_4113_ = v___x_4152_;
goto v___jp_4110_;
}
else
{
lean_object* v_toConstantVal_4153_; lean_object* v_numParams_4154_; lean_object* v_all_4155_; lean_object* v_numNested_4156_; lean_object* v_type_4157_; lean_object* v___x_4158_; 
v_toConstantVal_4153_ = lean_ctor_get(v_val_4150_, 0);
lean_inc_ref(v_toConstantVal_4153_);
v_numParams_4154_ = lean_ctor_get(v_val_4150_, 1);
lean_inc(v_numParams_4154_);
v_all_4155_ = lean_ctor_get(v_val_4150_, 3);
lean_inc(v_all_4155_);
v_numNested_4156_ = lean_ctor_get(v_val_4150_, 5);
lean_inc(v_numNested_4156_);
lean_dec_ref(v_val_4150_);
v_type_4157_ = lean_ctor_get(v_toConstantVal_4153_, 2);
lean_inc_ref(v_type_4157_);
lean_dec_ref(v_toConstantVal_4153_);
v___x_4158_ = l_Lean_Meta_isPropFormerType(v_type_4157_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; uint8_t v___x_4160_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4160_ = lean_unbox(v_a_4159_);
lean_dec(v_a_4159_);
if (v___x_4160_ == 0)
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_inc_n(v_indName_4005_, 2);
v___x_4161_ = l_Lean_mkRecName(v_indName_4005_);
v___x_4162_ = l_Lean_mkBRecOnName(v_indName_4005_);
lean_inc(v_all_4155_);
v___x_4163_ = lean_array_mk(v_all_4155_);
lean_inc(v___x_4162_);
lean_inc_ref(v___x_4163_);
lean_inc(v_numParams_4154_);
lean_inc(v___x_4161_);
v___x_4164_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4161_, v_numParams_4154_, v___x_4163_, v___x_4162_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
lean_dec_ref_known(v___x_4164_, 1);
v___x_4165_ = lean_unsigned_to_nat(0u);
v___x_4166_ = l_List_get_x21Internal___redArg(v___x_4015_, v_all_4155_, v___x_4165_);
lean_dec(v_all_4155_);
v___x_4167_ = lean_name_eq(v___x_4166_, v_indName_4005_);
lean_dec(v_indName_4005_);
lean_dec(v___x_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
lean_dec_ref(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v___x_4161_);
lean_dec(v_numNested_4156_);
lean_dec(v_numParams_4154_);
v___x_4168_ = lean_box(0);
v___y_4111_ = v_a_4144_;
v___y_4112_ = v___x_4147_;
v_a_4113_ = v___x_4168_;
goto v___jp_4110_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4169_ = lean_box(0);
v___x_4170_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4156_, v___x_4161_, v___x_4162_, v_numParams_4154_, v___x_4163_, v___x_4165_, v___x_4169_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_numNested_4156_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_dec_ref_known(v___x_4170_, 1);
v___y_4111_ = v_a_4144_;
v___y_4112_ = v___x_4147_;
v_a_4113_ = v___x_4169_;
goto v___jp_4110_;
}
else
{
lean_object* v_a_4171_; 
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___y_4116_ = v_a_4144_;
v___y_4117_ = v___x_4147_;
v_a_4118_ = v_a_4171_;
goto v___jp_4115_;
}
}
}
else
{
lean_object* v_a_4172_; 
lean_dec_ref(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v___x_4161_);
lean_dec(v_numNested_4156_);
lean_dec(v_all_4155_);
lean_dec(v_numParams_4154_);
lean_dec(v_indName_4005_);
v_a_4172_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4164_, 1);
v___y_4116_ = v_a_4144_;
v___y_4117_ = v___x_4147_;
v_a_4118_ = v_a_4172_;
goto v___jp_4115_;
}
}
else
{
lean_object* v___x_4173_; 
lean_dec(v_numNested_4156_);
lean_dec(v_all_4155_);
lean_dec(v_numParams_4154_);
lean_dec(v_indName_4005_);
v___x_4173_ = lean_box(0);
v___y_4111_ = v_a_4144_;
v___y_4112_ = v___x_4147_;
v_a_4113_ = v___x_4173_;
goto v___jp_4110_;
}
}
else
{
lean_object* v_a_4174_; 
lean_dec(v_numNested_4156_);
lean_dec(v_all_4155_);
lean_dec(v_numParams_4154_);
lean_dec(v_indName_4005_);
v_a_4174_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4158_, 1);
v___y_4116_ = v_a_4144_;
v___y_4117_ = v___x_4147_;
v_a_4118_ = v_a_4174_;
goto v___jp_4115_;
}
}
}
else
{
lean_object* v___x_4175_; 
lean_dec(v_a_4149_);
lean_dec(v_indName_4005_);
v___x_4175_ = lean_box(0);
v___y_4111_ = v_a_4144_;
v___y_4112_ = v___x_4147_;
v_a_4113_ = v___x_4175_;
goto v___jp_4110_;
}
}
else
{
lean_object* v_a_4176_; 
lean_dec(v_indName_4005_);
v_a_4176_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4148_, 1);
v___y_4116_ = v_a_4144_;
v___y_4117_ = v___x_4147_;
v_a_4118_ = v_a_4176_;
goto v___jp_4115_;
}
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_4005_);
v___x_4178_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
if (lean_obj_tag(v_a_4179_) == 5)
{
lean_object* v_val_4180_; uint8_t v_isRec_4181_; 
v_val_4180_ = lean_ctor_get(v_a_4179_, 0);
lean_inc_ref(v_val_4180_);
lean_dec_ref_known(v_a_4179_, 1);
v_isRec_4181_ = lean_ctor_get_uint8(v_val_4180_, sizeof(void*)*6);
if (v_isRec_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec_ref(v_val_4180_);
lean_dec(v_indName_4005_);
v___x_4182_ = lean_box(0);
v___y_4133_ = v___x_4177_;
v___y_4134_ = v_a_4144_;
v_a_4135_ = v___x_4182_;
goto v___jp_4132_;
}
else
{
lean_object* v_toConstantVal_4183_; lean_object* v_numParams_4184_; lean_object* v_all_4185_; lean_object* v_numNested_4186_; lean_object* v_type_4187_; lean_object* v___x_4188_; 
v_toConstantVal_4183_ = lean_ctor_get(v_val_4180_, 0);
lean_inc_ref(v_toConstantVal_4183_);
v_numParams_4184_ = lean_ctor_get(v_val_4180_, 1);
lean_inc(v_numParams_4184_);
v_all_4185_ = lean_ctor_get(v_val_4180_, 3);
lean_inc(v_all_4185_);
v_numNested_4186_ = lean_ctor_get(v_val_4180_, 5);
lean_inc(v_numNested_4186_);
lean_dec_ref(v_val_4180_);
v_type_4187_ = lean_ctor_get(v_toConstantVal_4183_, 2);
lean_inc_ref(v_type_4187_);
lean_dec_ref(v_toConstantVal_4183_);
v___x_4188_ = l_Lean_Meta_isPropFormerType(v_type_4187_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; uint8_t v___x_4190_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v___x_4190_ = lean_unbox(v_a_4189_);
lean_dec(v_a_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_inc_n(v_indName_4005_, 2);
v___x_4191_ = l_Lean_mkRecName(v_indName_4005_);
v___x_4192_ = l_Lean_mkBRecOnName(v_indName_4005_);
lean_inc(v_all_4185_);
v___x_4193_ = lean_array_mk(v_all_4185_);
lean_inc(v___x_4192_);
lean_inc_ref(v___x_4193_);
lean_inc(v_numParams_4184_);
lean_inc(v___x_4191_);
v___x_4194_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4191_, v_numParams_4184_, v___x_4193_, v___x_4192_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; uint8_t v___x_4197_; 
lean_dec_ref_known(v___x_4194_, 1);
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = l_List_get_x21Internal___redArg(v___x_4015_, v_all_4185_, v___x_4195_);
lean_dec(v_all_4185_);
v___x_4197_ = lean_name_eq(v___x_4196_, v_indName_4005_);
lean_dec(v_indName_4005_);
lean_dec(v___x_4196_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
lean_dec_ref(v___x_4193_);
lean_dec(v___x_4192_);
lean_dec(v___x_4191_);
lean_dec(v_numNested_4186_);
lean_dec(v_numParams_4184_);
v___x_4198_ = lean_box(0);
v___y_4133_ = v___x_4177_;
v___y_4134_ = v_a_4144_;
v_a_4135_ = v___x_4198_;
goto v___jp_4132_;
}
else
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = lean_box(0);
v___x_4200_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4186_, v___x_4191_, v___x_4192_, v_numParams_4184_, v___x_4193_, v___x_4195_, v___x_4199_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
lean_dec(v_numNested_4186_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_dec_ref_known(v___x_4200_, 1);
v___y_4133_ = v___x_4177_;
v___y_4134_ = v_a_4144_;
v_a_4135_ = v___x_4199_;
goto v___jp_4132_;
}
else
{
lean_object* v_a_4201_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___y_4138_ = v___x_4177_;
v___y_4139_ = v_a_4144_;
v_a_4140_ = v_a_4201_;
goto v___jp_4137_;
}
}
}
else
{
lean_object* v_a_4202_; 
lean_dec_ref(v___x_4193_);
lean_dec(v___x_4192_);
lean_dec(v___x_4191_);
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_4005_);
v_a_4202_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4194_, 1);
v___y_4138_ = v___x_4177_;
v___y_4139_ = v_a_4144_;
v_a_4140_ = v_a_4202_;
goto v___jp_4137_;
}
}
else
{
lean_object* v___x_4203_; 
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_4005_);
v___x_4203_ = lean_box(0);
v___y_4133_ = v___x_4177_;
v___y_4134_ = v_a_4144_;
v_a_4135_ = v___x_4203_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4204_; 
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_4005_);
v_a_4204_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4188_, 1);
v___y_4138_ = v___x_4177_;
v___y_4139_ = v_a_4144_;
v_a_4140_ = v_a_4204_;
goto v___jp_4137_;
}
}
}
else
{
lean_object* v___x_4205_; 
lean_dec(v_a_4179_);
lean_dec(v_indName_4005_);
v___x_4205_ = lean_box(0);
v___y_4133_ = v___x_4177_;
v___y_4134_ = v_a_4144_;
v_a_4135_ = v___x_4205_;
goto v___jp_4132_;
}
}
else
{
lean_object* v_a_4206_; 
lean_dec(v_indName_4005_);
v_a_4206_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4138_ = v___x_4177_;
v___y_4139_ = v_a_4144_;
v_a_4140_ = v_a_4206_;
goto v___jp_4137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Lean_mkBRecOn(v_indName_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v_inst_4295_, lean_object* v_R_4296_, lean_object* v_a_4297_, lean_object* v_b_4298_, lean_object* v_c_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4290_, v___x_4291_, v___x_4292_, v___x_4293_, v___x_4294_, v_a_4297_, v_b_4298_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v___x_4309_, lean_object* v___x_4310_, lean_object* v_inst_4311_, lean_object* v_R_4312_, lean_object* v_a_4313_, lean_object* v_b_4314_, lean_object* v_c_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4306_, v___x_4307_, v___x_4308_, v___x_4309_, v___x_4310_, v_inst_4311_, v_R_4312_, v_a_4313_, v_b_4314_, v_c_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v_upperBound_4306_);
return v_res_4321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v___x_4367_ = lean_unsigned_to_nat(2304625798u);
v___x_4368_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4369_ = l_Lean_Name_num___override(v___x_4368_, v___x_4367_);
return v___x_4369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4372_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4373_ = l_Lean_Name_str___override(v___x_4372_, v___x_4371_);
return v___x_4373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4376_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4377_ = l_Lean_Name_str___override(v___x_4376_, v___x_4375_);
return v___x_4377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4378_ = lean_unsigned_to_nat(2u);
v___x_4379_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4380_ = l_Lean_Name_num___override(v___x_4379_, v___x_4378_);
return v___x_4380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4382_; uint8_t v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4382_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4383_ = 0;
v___x_4384_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4385_ = l_Lean_registerTraceClass(v___x_4382_, v___x_4383_, v___x_4384_);
return v___x_4385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4387_;
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
