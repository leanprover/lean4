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
uint8_t v___x_1934__boxed_100_; lean_object* v_res_101_; 
v___x_1934__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_1934__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
uint8_t v___x_2089__boxed_251_; uint8_t v___x_2090__boxed_252_; lean_object* v_res_253_; 
v___x_2089__boxed_251_ = lean_unbox(v___x_239_);
v___x_2090__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2089__boxed_251_, v___x_2090__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
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
lean_object* v___f_435_; lean_object* v___x_4893__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_4893__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_4893__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
uint8_t v___x_8962__boxed_555_; lean_object* v_res_556_; 
v___x_8962__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_8962__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v___x_607_; lean_object* v_toCold_608_; lean_object* v_mctx_609_; lean_object* v_lctx_610_; lean_object* v_options_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v___x_607_ = lean_st_ref_get(v___y_601_);
v_toCold_608_ = lean_ctor_get(v___y_602_, 0);
v_mctx_609_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_mctx_609_);
lean_dec(v___x_607_);
v_lctx_610_ = lean_ctor_get(v___y_600_, 2);
v_options_611_ = lean_ctor_get(v_toCold_608_, 2);
lean_inc_ref(v_options_611_);
lean_inc_ref(v_lctx_610_);
v___x_612_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_612_, 0, v_env_606_);
lean_ctor_set(v___x_612_, 1, v_mctx_609_);
lean_ctor_set(v___x_612_, 2, v_lctx_610_);
lean_ctor_set(v___x_612_, 3, v_options_611_);
v___x_613_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v_msgData_599_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_ref_628_; lean_object* v___x_629_; lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_ref_628_ = lean_ctor_get(v___y_625_, 2);
v___x_629_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc(v_ref_628_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_ref_628_);
lean_ctor_set(v___x_634_, 1, v_a_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set_tag(v___x_632_, 1);
lean_ctor_set(v___x_632_, 0, v___x_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_650_ = lean_unsigned_to_nat(4u);
v___x_651_ = lean_unsigned_to_nat(68u);
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_654_ = l_mkPanicMessageWithDecl(v___x_653_, v___x_652_, v___x_651_, v___x_650_, v___x_649_);
return v___x_654_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_661_, lean_object* v_numMotives_662_, lean_object* v_numMinors_663_, lean_object* v___x_664_, lean_object* v_head_665_, lean_object* v_tail_666_, lean_object* v_recName_667_, lean_object* v_belowName_668_, lean_object* v_levelParams_669_, lean_object* v_refArgs_670_, lean_object* v_x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_677_ = lean_nat_add(v_nParams_661_, v_numMotives_662_);
v___x_678_ = lean_nat_add(v___x_677_, v_numMinors_663_);
v___x_679_ = lean_array_get_size(v_refArgs_670_);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
lean_dec(v_nParams_661_);
v___x_681_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_682_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_681_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v___x_682_;
}
else
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_683_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_661_);
lean_inc_ref_n(v_refArgs_670_, 4);
v___x_684_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_683_, v_nParams_661_);
v___x_685_ = l_Subarray_copy___redArg(v___x_684_);
lean_inc(v___x_677_);
v___x_686_ = l_Array_toSubarray___redArg(v_refArgs_670_, v_nParams_661_, v___x_677_);
v___x_687_ = l_Subarray_copy___redArg(v___x_686_);
lean_inc_n(v___x_678_, 2);
v___x_688_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_677_, v___x_678_);
v___x_689_ = l_Subarray_copy___redArg(v___x_688_);
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v___x_679_, v___x_690_);
lean_inc(v___x_691_);
v___x_692_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_678_, v___x_691_);
v___x_693_ = l_Subarray_copy___redArg(v___x_692_);
v___x_694_ = lean_array_get(v___x_664_, v_refArgs_670_, v___x_691_);
lean_dec(v___x_691_);
lean_dec_ref(v_refArgs_670_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___x_694_);
v___x_695_ = lean_infer_type(v___x_694_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_697_ = lean_infer_type(v_a_696_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l_Lean_Meta_typeFormerTypeLevel(v_a_698_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
if (lean_obj_tag(v_a_700_) == 1)
{
lean_object* v_val_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; size_t v_sz_707_; size_t v___x_708_; lean_object* v___x_709_; 
v_val_701_ = lean_ctor_get(v_a_700_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_a_700_, 1);
v___x_702_ = l_Lean_mkLevelMax(v_val_701_, v_head_665_);
lean_inc_n(v___x_702_, 2);
v___x_703_ = l_Lean_Level_succ___override(v___x_702_);
v___x_704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_tail_666_);
v___x_705_ = l_Lean_Expr_const___override(v_recName_667_, v___x_704_);
v___x_706_ = l_Lean_mkAppN(v___x_705_, v___x_685_);
v_sz_707_ = lean_array_size(v___x_687_);
v___x_708_ = ((size_t)0ULL);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_702_, v___x_678_, v___x_679_, v___x_687_, v_sz_707_, v___x_708_, v___x_706_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___x_678_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; size_t v_sz_711_; lean_object* v___x_712_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_sz_711_ = lean_array_size(v___x_689_);
lean_inc_ref(v___x_687_);
lean_inc(v___x_702_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_702_, v___x_687_, v___x_689_, v_sz_711_, v___x_708_, v_a_710_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec_ref(v___x_689_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = l_Lean_mkAppN(v_a_713_, v___x_693_);
lean_inc(v___x_694_);
v___x_715_ = l_Lean_Expr_app___override(v___x_714_, v___x_694_);
v___x_716_ = l_Array_append___redArg(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
v___x_717_ = l_Array_append___redArg(v___x_716_, v___x_693_);
lean_dec_ref(v___x_693_);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_690_);
v___x_719_ = lean_array_push(v___x_718_, v___x_694_);
v___x_720_ = l_Array_append___redArg(v___x_717_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = l_Lean_Expr_sort___override(v___x_702_);
v___x_722_ = 0;
v___x_723_ = 1;
v___x_724_ = l_Lean_Meta_mkForallFVars(v___x_720_, v___x_721_, v___x_722_, v___x_680_, v___x_680_, v___x_723_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = l_Lean_Meta_mkLambdaFVars(v___x_720_, v___x_715_, v___x_722_, v___x_680_, v___x_722_, v___x_680_, v___x_723_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec_ref(v___x_720_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = lean_box(1);
v___x_729_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_668_, v_levelParams_669_, v_a_725_, v_a_727_, v___x_728_, v___y_675_);
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec(v_a_725_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_730_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_726_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_726_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v___x_720_);
lean_dec_ref(v___x_715_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_738_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_724_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_724_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v___x_702_);
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_746_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_712_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_712_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v___x_702_);
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_754_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_709_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_709_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_a_700_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_678_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
v___x_762_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_763_ = l_Lean_MessageData_ofExpr(v___x_694_);
v___x_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_764_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_766_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v___x_767_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_678_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
v_a_768_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_699_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_699_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_678_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
v_a_776_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_697_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_697_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec_ref(v___x_689_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_678_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
v_a_784_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_695_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_695_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_792_, lean_object* v_numMotives_793_, lean_object* v_numMinors_794_, lean_object* v___x_795_, lean_object* v_head_796_, lean_object* v_tail_797_, lean_object* v_recName_798_, lean_object* v_belowName_799_, lean_object* v_levelParams_800_, lean_object* v_refArgs_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_792_, v_numMotives_793_, v_numMinors_794_, v___x_795_, v_head_796_, v_tail_797_, v_recName_798_, v_belowName_799_, v_levelParams_800_, v_refArgs_801_, v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_x_802_);
lean_dec_ref(v___x_795_);
lean_dec(v_numMinors_794_);
lean_dec(v_numMotives_793_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = l_List_reverse___redArg(v_a_810_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_head_812_ = lean_ctor_get(v_a_809_, 0);
v_tail_813_ = lean_ctor_get(v_a_809_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_809_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_a_809_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_head_812_);
lean_dec(v_a_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Lean_Level_param___override(v_head_812_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_a_810_);
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_810_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_a_809_ = v_tail_813_;
v_a_810_ = v___x_819_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_823_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v___x_828_);
lean_ctor_set(v___x_829_, 3, v___x_828_);
lean_ctor_set(v___x_829_, 4, v___x_828_);
lean_ctor_set(v___x_829_, 5, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_830_, uint8_t v_s_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; lean_object* v_nextMacroScope_837_; lean_object* v_ngen_838_; lean_object* v_auxDeclNGen_839_; lean_object* v_traceState_840_; lean_object* v_messages_841_; lean_object* v_infoState_842_; lean_object* v_snapshotTasks_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_872_; 
v___x_835_ = lean_st_ref_take(v___y_833_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
v_nextMacroScope_837_ = lean_ctor_get(v___x_835_, 1);
v_ngen_838_ = lean_ctor_get(v___x_835_, 2);
v_auxDeclNGen_839_ = lean_ctor_get(v___x_835_, 3);
v_traceState_840_ = lean_ctor_get(v___x_835_, 4);
v_messages_841_ = lean_ctor_get(v___x_835_, 6);
v_infoState_842_ = lean_ctor_get(v___x_835_, 7);
v_snapshotTasks_843_ = lean_ctor_get(v___x_835_, 8);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___x_835_, 5);
lean_dec(v_unused_873_);
v___x_845_ = v___x_835_;
v_isShared_846_ = v_isSharedCheck_872_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_snapshotTasks_843_);
lean_inc(v_infoState_842_);
lean_inc(v_messages_841_);
lean_inc(v_traceState_840_);
lean_inc(v_auxDeclNGen_839_);
lean_inc(v_ngen_838_);
lean_inc(v_nextMacroScope_837_);
lean_inc(v_env_836_);
lean_dec(v___x_835_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_872_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_847_ = 0;
v___x_848_ = lean_box(0);
v___x_849_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_836_, v_declName_830_, v_s_831_, v___x_847_, v___x_848_);
v___x_850_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 5, v___x_850_);
lean_ctor_set(v___x_845_, 0, v___x_849_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_nextMacroScope_837_);
lean_ctor_set(v_reuseFailAlloc_871_, 2, v_ngen_838_);
lean_ctor_set(v_reuseFailAlloc_871_, 3, v_auxDeclNGen_839_);
lean_ctor_set(v_reuseFailAlloc_871_, 4, v_traceState_840_);
lean_ctor_set(v_reuseFailAlloc_871_, 5, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_871_, 6, v_messages_841_);
lean_ctor_set(v_reuseFailAlloc_871_, 7, v_infoState_842_);
lean_ctor_set(v_reuseFailAlloc_871_, 8, v_snapshotTasks_843_);
v___x_852_ = v_reuseFailAlloc_871_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_mctx_855_; lean_object* v_zetaDeltaFVarIds_856_; lean_object* v_postponed_857_; lean_object* v_diag_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_869_; 
v___x_853_ = lean_st_ref_put(v___y_833_, v___x_852_);
v___x_854_ = lean_st_ref_take(v___y_832_);
v_mctx_855_ = lean_ctor_get(v___x_854_, 0);
v_zetaDeltaFVarIds_856_ = lean_ctor_get(v___x_854_, 2);
v_postponed_857_ = lean_ctor_get(v___x_854_, 3);
v_diag_858_ = lean_ctor_get(v___x_854_, 4);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v___x_854_, 1);
lean_dec(v_unused_870_);
v___x_860_ = v___x_854_;
v_isShared_861_ = v_isSharedCheck_869_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_diag_858_);
lean_inc(v_postponed_857_);
lean_inc(v_zetaDeltaFVarIds_856_);
lean_inc(v_mctx_855_);
lean_dec(v___x_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_869_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_863_);
v___x_865_ = v___x_860_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_mctx_855_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_zetaDeltaFVarIds_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_postponed_857_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_diag_858_);
v___x_865_ = v_reuseFailAlloc_868_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_st_ref_put(v___y_832_, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_862_);
return v___x_867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_874_, lean_object* v_s_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_s_boxed_879_; lean_object* v_res_880_; 
v_s_boxed_879_ = lean_unbox(v_s_875_);
v_res_880_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_874_, v_s_boxed_879_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec(v___y_876_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v___x_887_; lean_object* v___x_888_; 
v___x_887_ = 0;
v___x_888_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_881_, v___x_887_, v___y_883_, v___y_885_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_896_, lean_object* v_msg_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_toCold_903_; lean_object* v_currRecDepth_904_; lean_object* v_ref_905_; uint8_t v_diag_906_; uint8_t v_suppressElabErrors_907_; lean_object* v_ref_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_toCold_903_ = lean_ctor_get(v___y_900_, 0);
v_currRecDepth_904_ = lean_ctor_get(v___y_900_, 1);
v_ref_905_ = lean_ctor_get(v___y_900_, 2);
v_diag_906_ = lean_ctor_get_uint8(v___y_900_, sizeof(void*)*3);
v_suppressElabErrors_907_ = lean_ctor_get_uint8(v___y_900_, sizeof(void*)*3 + 1);
v_ref_908_ = l_Lean_replaceRef(v_ref_896_, v_ref_905_);
lean_inc(v_currRecDepth_904_);
lean_inc_ref(v_toCold_903_);
v___x_909_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_909_, 0, v_toCold_903_);
lean_ctor_set(v___x_909_, 1, v_currRecDepth_904_);
lean_ctor_set(v___x_909_, 2, v_ref_908_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*3, v_diag_906_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*3 + 1, v_suppressElabErrors_907_);
v___x_910_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_897_, v___y_898_, v___y_899_, v___x_909_, v___y_901_);
lean_dec_ref_known(v___x_909_, 3);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_911_, lean_object* v_msg_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_911_, v_msg_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v_ref_911_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
lean_ctor_set(v___x_923_, 2, v___x_922_);
lean_ctor_set(v___x_923_, 3, v___x_922_);
lean_ctor_set(v___x_923_, 4, v___x_921_);
lean_ctor_set(v___x_923_, 5, v___x_921_);
lean_ctor_set(v___x_923_, 6, v___x_921_);
lean_ctor_set(v___x_923_, 7, v___x_921_);
lean_ctor_set(v___x_923_, 8, v___x_921_);
lean_ctor_set(v___x_923_, 9, v___x_921_);
lean_ctor_set(v___x_923_, 10, v___x_921_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_unsigned_to_nat(32u);
v___x_925_ = lean_mk_empty_array_with_capacity(v___x_924_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_927_ = ((size_t)5ULL);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_unsigned_to_nat(32u);
v___x_930_ = lean_mk_empty_array_with_capacity(v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_932_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_930_);
lean_ctor_set(v___x_932_, 2, v___x_928_);
lean_ctor_set(v___x_932_, 3, v___x_928_);
lean_ctor_set_usize(v___x_932_, 4, v___x_927_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_933_ = lean_box(1);
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_934_);
lean_ctor_set(v___x_936_, 2, v___x_933_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_939_ = l_Lean_stringToMessageData(v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_958_, lean_object* v_declHint_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v_env_964_; uint8_t v___x_965_; 
v___x_962_ = lean_box(0);
v___x_963_ = lean_st_ref_get(v___y_960_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Name_isAnonymous(v_declHint_959_);
if (v___x_965_ == 0)
{
uint8_t v_isExporting_966_; 
v_isExporting_966_ = lean_ctor_get_uint8(v_env_964_, sizeof(void*)*8);
if (v_isExporting_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_959_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_msg_958_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; uint8_t v___x_969_; 
lean_inc_ref(v_env_964_);
v___x_968_ = l_Lean_Environment_setExporting(v_env_964_, v___x_965_);
lean_inc(v_declHint_959_);
lean_inc_ref(v___x_968_);
v___x_969_ = l_Lean_Environment_contains(v___x_968_, v_declHint_959_, v_isExporting_966_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec_ref(v___x_968_);
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_959_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_msg_958_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_c_976_; lean_object* v___x_977_; 
v___x_971_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_973_ = l_Lean_Options_empty;
v___x_974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_974_, 0, v___x_968_);
lean_ctor_set(v___x_974_, 1, v___x_971_);
lean_ctor_set(v___x_974_, 2, v___x_972_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
lean_inc(v_declHint_959_);
v___x_975_ = l_Lean_MessageData_ofConstName(v_declHint_959_, v___x_965_);
v_c_976_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_976_, 0, v___x_974_);
lean_ctor_set(v_c_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_964_, v_declHint_959_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_959_);
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_c_976_);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_MessageData_note(v___x_981_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v_msg_958_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1019_; 
v_val_985_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_987_ = v___x_977_;
v_isShared_988_ = v_isSharedCheck_1019_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v___x_977_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1019_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_mod_991_; uint8_t v___x_992_; 
v___x_989_ = l_Lean_Environment_header(v_env_964_);
lean_dec_ref(v_env_964_);
v___x_990_ = l_Lean_EnvironmentHeader_moduleNames(v___x_989_);
v_mod_991_ = lean_array_get(v___x_962_, v___x_990_, v_val_985_);
lean_dec(v_val_985_);
lean_dec_ref(v___x_990_);
v___x_992_ = l_Lean_isPrivateName(v_declHint_959_);
lean_dec(v_declHint_959_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_c_976_);
v___x_995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = l_Lean_MessageData_ofName(v_mod_991_);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_MessageData_note(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_msg_958_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_1002_);
v___x_1004_ = v___x_987_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v_c_976_);
v___x_1008_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_MessageData_ofName(v_mod_991_);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_MessageData_note(v___x_1013_);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_msg_958_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_1015_);
v___x_1017_ = v___x_987_;
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
}
}
}
}
}
else
{
lean_object* v___x_1020_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_959_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_958_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1021_, lean_object* v_declHint_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1021_, v_declHint_1022_, v___y_1023_);
lean_dec(v___y_1023_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1026_, lean_object* v_declHint_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1043_; 
v___x_1033_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1026_, v_declHint_1027_, v___y_1031_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1043_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1038_ = l_Lean_unknownIdentifierMessageTag;
v___x_1039_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_a_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1044_, lean_object* v_declHint_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1044_, v_declHint_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1052_, lean_object* v_msg_1053_, lean_object* v_declHint_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1062_; 
v___x_1060_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1053_, v_declHint_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1052_, v_a_1061_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1063_, lean_object* v_msg_1064_, lean_object* v_declHint_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1063_, v_msg_1064_, v_declHint_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v_ref_1063_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1078_, lean_object* v_constName_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1085_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1086_ = 0;
lean_inc(v_constName_1079_);
v___x_1087_ = l_Lean_MessageData_ofConstName(v_constName_1079_, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1085_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1078_, v___x_1090_, v_constName_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1092_, lean_object* v_constName_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1092_, v_constName_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_ref_1092_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_ref_1106_; lean_object* v___x_1107_; 
v_ref_1106_ = lean_ctor_get(v___y_1103_, 2);
v___x_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1106_, v_constName_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1121_ = lean_st_ref_get(v___y_1119_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = 0;
lean_inc(v_constName_1115_);
v___x_1124_ = l_Lean_Environment_find_x3f(v_env_1122_, v_constName_1115_, v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1125_;
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
lean_dec(v_constName_1115_);
v_val_1126_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1124_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v___x_1124_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 0);
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_val_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1143_ = l_Lean_stringToMessageData(v___x_1142_);
return v___x_1143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1150_, lean_object* v_nParams_1151_, lean_object* v_belowName_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Lean_instInhabitedExpr;
lean_inc(v_recName_1150_);
v___x_1159_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1150_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
if (lean_obj_tag(v_a_1160_) == 7)
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1276_; 
v_val_1161_ = lean_ctor_get(v_a_1160_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_a_1160_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1163_ = v_a_1160_;
v_isShared_1164_ = v_isSharedCheck_1276_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v_a_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1276_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_toConstantVal_1165_; lean_object* v_numMotives_1166_; lean_object* v_numMinors_1167_; lean_object* v_levelParams_1168_; lean_object* v_type_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_toConstantVal_1165_ = lean_ctor_get(v_val_1161_, 0);
lean_inc_ref(v_toConstantVal_1165_);
v_numMotives_1166_ = lean_ctor_get(v_val_1161_, 4);
lean_inc(v_numMotives_1166_);
v_numMinors_1167_ = lean_ctor_get(v_val_1161_, 5);
lean_inc(v_numMinors_1167_);
lean_dec_ref(v_val_1161_);
v_levelParams_1168_ = lean_ctor_get(v_toConstantVal_1165_, 1);
lean_inc_n(v_levelParams_1168_, 2);
v_type_1169_ = lean_ctor_get(v_toConstantVal_1165_, 2);
lean_inc_ref(v_type_1169_);
lean_dec_ref(v_toConstantVal_1165_);
v___x_1170_ = lean_box(0);
v___x_1171_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1168_, v___x_1170_);
if (lean_obj_tag(v___x_1171_) == 1)
{
lean_object* v_head_1172_; lean_object* v_tail_1173_; lean_object* v___f_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; 
v_head_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_head_1172_);
v_tail_1173_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_tail_1173_);
lean_dec_ref_known(v___x_1171_, 2);
v___f_1174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1174_, 0, v_nParams_1151_);
lean_closure_set(v___f_1174_, 1, v_numMotives_1166_);
lean_closure_set(v___f_1174_, 2, v_numMinors_1167_);
lean_closure_set(v___f_1174_, 3, v___x_1158_);
lean_closure_set(v___f_1174_, 4, v_head_1172_);
lean_closure_set(v___f_1174_, 5, v_tail_1173_);
lean_closure_set(v___f_1174_, 6, v_recName_1150_);
lean_closure_set(v___f_1174_, 7, v_belowName_1152_);
lean_closure_set(v___f_1174_, 8, v_levelParams_1168_);
v___x_1175_ = 0;
v___x_1176_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1169_, v___f_1174_, v___x_1175_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc_n(v_a_1177_, 2);
lean_dec_ref_known(v___x_1176_, 1);
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 1);
lean_ctor_set(v___x_1163_, 0, v_a_1177_);
v___x_1179_ = v___x_1163_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1177_);
v___x_1179_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_addDecl(v___x_1179_, v___x_1175_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_toConstantVal_1181_; lean_object* v_name_1182_; lean_object* v___x_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref_known(v___x_1180_, 1);
v_toConstantVal_1181_ = lean_ctor_get(v_a_1177_, 0);
lean_inc_ref(v_toConstantVal_1181_);
lean_dec(v_a_1177_);
v_name_1182_ = lean_ctor_get(v_toConstantVal_1181_, 0);
lean_inc_n(v_name_1182_, 2);
lean_dec_ref(v_toConstantVal_1181_);
v___x_1183_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1182_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1183_, 0);
lean_dec(v_unused_1260_);
v___x_1185_ = v___x_1183_;
v_isShared_1186_ = v_isSharedCheck_1259_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v___x_1183_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1259_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v_env_1188_; lean_object* v_nextMacroScope_1189_; lean_object* v_ngen_1190_; lean_object* v_auxDeclNGen_1191_; lean_object* v_traceState_1192_; lean_object* v_messages_1193_; lean_object* v_infoState_1194_; lean_object* v_snapshotTasks_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1257_; 
v___x_1187_ = lean_st_ref_take(v_a_1156_);
v_env_1188_ = lean_ctor_get(v___x_1187_, 0);
v_nextMacroScope_1189_ = lean_ctor_get(v___x_1187_, 1);
v_ngen_1190_ = lean_ctor_get(v___x_1187_, 2);
v_auxDeclNGen_1191_ = lean_ctor_get(v___x_1187_, 3);
v_traceState_1192_ = lean_ctor_get(v___x_1187_, 4);
v_messages_1193_ = lean_ctor_get(v___x_1187_, 6);
v_infoState_1194_ = lean_ctor_get(v___x_1187_, 7);
v_snapshotTasks_1195_ = lean_ctor_get(v___x_1187_, 8);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; 
v_unused_1258_ = lean_ctor_get(v___x_1187_, 5);
lean_dec(v_unused_1258_);
v___x_1197_ = v___x_1187_;
v_isShared_1198_ = v_isSharedCheck_1257_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snapshotTasks_1195_);
lean_inc(v_infoState_1194_);
lean_inc(v_messages_1193_);
lean_inc(v_traceState_1192_);
lean_inc(v_auxDeclNGen_1191_);
lean_inc(v_ngen_1190_);
lean_inc(v_nextMacroScope_1189_);
lean_inc(v_env_1188_);
lean_dec(v___x_1187_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1257_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
lean_inc(v_name_1182_);
v___x_1199_ = l_Lean_markAuxRecursor(v_env_1188_, v_name_1182_);
v___x_1200_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 5, v___x_1200_);
lean_ctor_set(v___x_1197_, 0, v___x_1199_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_nextMacroScope_1189_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_ngen_1190_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_auxDeclNGen_1191_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_traceState_1192_);
lean_ctor_set(v_reuseFailAlloc_1256_, 5, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1256_, 6, v_messages_1193_);
lean_ctor_set(v_reuseFailAlloc_1256_, 7, v_infoState_1194_);
lean_ctor_set(v_reuseFailAlloc_1256_, 8, v_snapshotTasks_1195_);
v___x_1202_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_mctx_1205_; lean_object* v_zetaDeltaFVarIds_1206_; lean_object* v_postponed_1207_; lean_object* v_diag_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1254_; 
v___x_1203_ = lean_st_ref_put(v_a_1156_, v___x_1202_);
v___x_1204_ = lean_st_ref_take(v_a_1154_);
v_mctx_1205_ = lean_ctor_get(v___x_1204_, 0);
v_zetaDeltaFVarIds_1206_ = lean_ctor_get(v___x_1204_, 2);
v_postponed_1207_ = lean_ctor_get(v___x_1204_, 3);
v_diag_1208_ = lean_ctor_get(v___x_1204_, 4);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1204_, 1);
lean_dec(v_unused_1255_);
v___x_1210_ = v___x_1204_;
v_isShared_1211_ = v_isSharedCheck_1254_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_diag_1208_);
lean_inc(v_postponed_1207_);
lean_inc(v_zetaDeltaFVarIds_1206_);
lean_inc(v_mctx_1205_);
lean_dec(v___x_1204_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1254_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 1, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_mctx_1205_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1253_, 2, v_zetaDeltaFVarIds_1206_);
lean_ctor_set(v_reuseFailAlloc_1253_, 3, v_postponed_1207_);
lean_ctor_set(v_reuseFailAlloc_1253_, 4, v_diag_1208_);
v___x_1214_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_env_1217_; lean_object* v_nextMacroScope_1218_; lean_object* v_ngen_1219_; lean_object* v_auxDeclNGen_1220_; lean_object* v_traceState_1221_; lean_object* v_messages_1222_; lean_object* v_infoState_1223_; lean_object* v_snapshotTasks_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1251_; 
v___x_1215_ = lean_st_ref_put(v_a_1154_, v___x_1214_);
v___x_1216_ = lean_st_ref_take(v_a_1156_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
v_nextMacroScope_1218_ = lean_ctor_get(v___x_1216_, 1);
v_ngen_1219_ = lean_ctor_get(v___x_1216_, 2);
v_auxDeclNGen_1220_ = lean_ctor_get(v___x_1216_, 3);
v_traceState_1221_ = lean_ctor_get(v___x_1216_, 4);
v_messages_1222_ = lean_ctor_get(v___x_1216_, 6);
v_infoState_1223_ = lean_ctor_get(v___x_1216_, 7);
v_snapshotTasks_1224_ = lean_ctor_get(v___x_1216_, 8);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1216_, 5);
lean_dec(v_unused_1252_);
v___x_1226_ = v___x_1216_;
v_isShared_1227_ = v_isSharedCheck_1251_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snapshotTasks_1224_);
lean_inc(v_infoState_1223_);
lean_inc(v_messages_1222_);
lean_inc(v_traceState_1221_);
lean_inc(v_auxDeclNGen_1220_);
lean_inc(v_ngen_1219_);
lean_inc(v_nextMacroScope_1218_);
lean_inc(v_env_1217_);
lean_dec(v___x_1216_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1251_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1228_ = l_Lean_addProtected(v_env_1217_, v_name_1182_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 5, v___x_1200_);
lean_ctor_set(v___x_1226_, 0, v___x_1228_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_nextMacroScope_1218_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_ngen_1219_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_auxDeclNGen_1220_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_traceState_1221_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_messages_1222_);
lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_infoState_1223_);
lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_snapshotTasks_1224_);
v___x_1230_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_mctx_1233_; lean_object* v_zetaDeltaFVarIds_1234_; lean_object* v_postponed_1235_; lean_object* v_diag_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1248_; 
v___x_1231_ = lean_st_ref_put(v_a_1156_, v___x_1230_);
v___x_1232_ = lean_st_ref_take(v_a_1154_);
v_mctx_1233_ = lean_ctor_get(v___x_1232_, 0);
v_zetaDeltaFVarIds_1234_ = lean_ctor_get(v___x_1232_, 2);
v_postponed_1235_ = lean_ctor_get(v___x_1232_, 3);
v_diag_1236_ = lean_ctor_get(v___x_1232_, 4);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1232_, 1);
lean_dec(v_unused_1249_);
v___x_1238_ = v___x_1232_;
v_isShared_1239_ = v_isSharedCheck_1248_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_diag_1236_);
lean_inc(v_postponed_1235_);
lean_inc(v_zetaDeltaFVarIds_1234_);
lean_inc(v_mctx_1233_);
lean_dec(v___x_1232_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1248_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1212_);
v___x_1242_ = v___x_1238_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_mctx_1233_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_zetaDeltaFVarIds_1234_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_postponed_1235_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v_diag_1236_);
v___x_1242_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_st_ref_put(v_a_1154_, v___x_1242_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1240_);
v___x_1245_ = v___x_1185_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
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
lean_dec(v_a_1177_);
return v___x_1180_;
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_del_object(v___x_1163_);
v_a_1262_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1176_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1176_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_dec(v___x_1171_);
lean_dec_ref(v_type_1169_);
lean_dec(v_levelParams_1168_);
lean_dec(v_numMinors_1167_);
lean_dec(v_numMotives_1166_);
lean_del_object(v___x_1163_);
lean_dec(v_belowName_1152_);
lean_dec(v_nParams_1151_);
v___x_1270_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1271_ = l_Lean_MessageData_ofName(v_recName_1150_);
v___x_1272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1270_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1272_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1274_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
return v___x_1275_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_a_1160_);
lean_dec(v_belowName_1152_);
lean_dec(v_nParams_1151_);
v___x_1277_ = l_Lean_MessageData_ofName(v_recName_1150_);
v___x_1278_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1279_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
return v___x_1280_;
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_belowName_1152_);
lean_dec(v_nParams_1151_);
lean_dec(v_recName_1150_);
v_a_1281_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1159_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1159_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1289_, lean_object* v_nParams_1290_, lean_object* v_belowName_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1289_, v_nParams_1290_, v_belowName_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1298_, lean_object* v_msg_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1306_, v_msg_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1314_, uint8_t v_s_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1314_, v_s_1315_, v___y_1317_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1322_, lean_object* v_s_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
uint8_t v_s_boxed_1329_; lean_object* v_res_1330_; 
v_s_boxed_1329_ = lean_unbox(v_s_1323_);
v_res_1330_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1322_, v_s_boxed_1329_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1331_, lean_object* v_constName_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_constName_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1339_, v_constName_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1347_, lean_object* v_ref_1348_, lean_object* v_constName_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1348_, v_constName_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_ref_1357_, lean_object* v_constName_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1356_, v_ref_1357_, v_constName_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v_ref_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1365_, lean_object* v_ref_1366_, lean_object* v_msg_1367_, lean_object* v_declHint_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1366_, v_msg_1367_, v_declHint_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1375_, lean_object* v_ref_1376_, lean_object* v_msg_1377_, lean_object* v_declHint_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1375_, v_ref_1376_, v_msg_1377_, v_declHint_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v_ref_1376_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1385_, lean_object* v_declHint_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1385_, v_declHint_1386_, v___y_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1393_, lean_object* v_declHint_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1393_, v_declHint_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1401_, lean_object* v_ref_1402_, lean_object* v_msg_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1402_, v_msg_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_ref_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1410_, v_ref_1411_, v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v_ref_1411_);
return v_res_1418_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_unsigned_to_nat(32u);
v___x_1420_ = lean_mk_empty_array_with_capacity(v___x_1419_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1422_ = ((size_t)5ULL);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_unsigned_to_nat(32u);
v___x_1425_ = lean_mk_empty_array_with_capacity(v___x_1424_);
v___x_1426_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1427_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v___x_1425_);
lean_ctor_set(v___x_1427_, 2, v___x_1423_);
lean_ctor_set(v___x_1427_, 3, v___x_1423_);
lean_ctor_set_usize(v___x_1427_, 4, v___x_1422_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v_traceState_1431_; lean_object* v_traces_1432_; lean_object* v___x_1433_; lean_object* v_traceState_1434_; lean_object* v_env_1435_; lean_object* v_nextMacroScope_1436_; lean_object* v_ngen_1437_; lean_object* v_auxDeclNGen_1438_; lean_object* v_cache_1439_; lean_object* v_messages_1440_; lean_object* v_infoState_1441_; lean_object* v_snapshotTasks_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1461_; 
v___x_1430_ = lean_st_ref_get(v___y_1428_);
v_traceState_1431_ = lean_ctor_get(v___x_1430_, 4);
lean_inc_ref(v_traceState_1431_);
lean_dec(v___x_1430_);
v_traces_1432_ = lean_ctor_get(v_traceState_1431_, 0);
lean_inc_ref(v_traces_1432_);
lean_dec_ref(v_traceState_1431_);
v___x_1433_ = lean_st_ref_take(v___y_1428_);
v_traceState_1434_ = lean_ctor_get(v___x_1433_, 4);
v_env_1435_ = lean_ctor_get(v___x_1433_, 0);
v_nextMacroScope_1436_ = lean_ctor_get(v___x_1433_, 1);
v_ngen_1437_ = lean_ctor_get(v___x_1433_, 2);
v_auxDeclNGen_1438_ = lean_ctor_get(v___x_1433_, 3);
v_cache_1439_ = lean_ctor_get(v___x_1433_, 5);
v_messages_1440_ = lean_ctor_get(v___x_1433_, 6);
v_infoState_1441_ = lean_ctor_get(v___x_1433_, 7);
v_snapshotTasks_1442_ = lean_ctor_get(v___x_1433_, 8);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1444_ = v___x_1433_;
v_isShared_1445_ = v_isSharedCheck_1461_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snapshotTasks_1442_);
lean_inc(v_infoState_1441_);
lean_inc(v_messages_1440_);
lean_inc(v_cache_1439_);
lean_inc(v_traceState_1434_);
lean_inc(v_auxDeclNGen_1438_);
lean_inc(v_ngen_1437_);
lean_inc(v_nextMacroScope_1436_);
lean_inc(v_env_1435_);
lean_dec(v___x_1433_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1461_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
uint64_t v_tid_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1459_; 
v_tid_1446_ = lean_ctor_get_uint64(v_traceState_1434_, sizeof(void*)*1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_traceState_1434_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_traceState_1434_, 0);
lean_dec(v_unused_1460_);
v___x_1448_ = v_traceState_1434_;
v_isShared_1449_ = v_isSharedCheck_1459_;
goto v_resetjp_1447_;
}
else
{
lean_dec(v_traceState_1434_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1459_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1450_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1452_ = v___x_1448_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1450_);
lean_ctor_set_uint64(v_reuseFailAlloc_1458_, sizeof(void*)*1, v_tid_1446_);
v___x_1452_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
lean_object* v___x_1454_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v___x_1452_);
v___x_1454_ = v___x_1444_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_env_1435_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_nextMacroScope_1436_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_ngen_1437_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_auxDeclNGen_1438_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v_cache_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 6, v_messages_1440_);
lean_ctor_set(v_reuseFailAlloc_1457_, 7, v_infoState_1441_);
lean_ctor_set(v_reuseFailAlloc_1457_, 8, v_snapshotTasks_1442_);
v___x_1454_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_st_ref_put(v___y_1428_, v___x_1454_);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v_traces_1432_);
return v___x_1456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1462_);
lean_dec(v___y_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1477_, lean_object* v_opt_1478_){
_start:
{
lean_object* v_name_1479_; lean_object* v_defValue_1480_; lean_object* v_map_1481_; lean_object* v___x_1482_; 
v_name_1479_ = lean_ctor_get(v_opt_1478_, 0);
v_defValue_1480_ = lean_ctor_get(v_opt_1478_, 1);
v_map_1481_ = lean_ctor_get(v_opts_1477_, 0);
v___x_1482_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1481_, v_name_1479_);
if (lean_obj_tag(v___x_1482_) == 0)
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_unbox(v_defValue_1480_);
return v___x_1483_;
}
else
{
lean_object* v_val_1484_; 
v_val_1484_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1484_);
lean_dec_ref_known(v___x_1482_, 1);
if (lean_obj_tag(v_val_1484_) == 1)
{
uint8_t v_v_1485_; 
v_v_1485_ = lean_ctor_get_uint8(v_val_1484_, 0);
lean_dec_ref_known(v_val_1484_, 0);
return v_v_1485_;
}
else
{
uint8_t v___x_1486_; 
lean_dec(v_val_1484_);
v___x_1486_ = lean_unbox(v_defValue_1480_);
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1487_, lean_object* v_opt_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1487_, v_opt_1488_);
lean_dec_ref(v_opt_1488_);
lean_dec_ref(v_opts_1487_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l_Lean_MessageData_ofName(v_indName_1491_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1500_, lean_object* v_x_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_Lean_mkBelow___lam__0(v_indName_1500_, v_x_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec_ref(v_x_1501_);
return v_res_1507_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1508_){
_start:
{
if (lean_obj_tag(v_e_1508_) == 0)
{
uint8_t v___x_1509_; 
v___x_1509_ = 2;
return v___x_1509_;
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1511_);
lean_dec_ref(v_e_1511_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1514_){
_start:
{
if (lean_obj_tag(v_x_1514_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
v_a_1516_ = lean_ctor_get(v_x_1514_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1514_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v_x_1514_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v_x_1514_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v_a_1524_ = lean_ctor_get(v_x_1514_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_x_1514_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v_x_1514_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v_x_1514_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 0);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1535_, lean_object* v_opt_1536_){
_start:
{
lean_object* v_name_1537_; lean_object* v_defValue_1538_; lean_object* v_map_1539_; lean_object* v___x_1540_; 
v_name_1537_ = lean_ctor_get(v_opt_1536_, 0);
v_defValue_1538_ = lean_ctor_get(v_opt_1536_, 1);
v_map_1539_ = lean_ctor_get(v_opts_1535_, 0);
v___x_1540_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1539_, v_name_1537_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_inc(v_defValue_1538_);
return v_defValue_1538_;
}
else
{
lean_object* v_val_1541_; 
v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1540_, 1);
if (lean_obj_tag(v_val_1541_) == 3)
{
lean_object* v_v_1542_; 
v_v_1542_ = lean_ctor_get(v_val_1541_, 0);
lean_inc(v_v_1542_);
lean_dec_ref_known(v_val_1541_, 1);
return v_v_1542_;
}
else
{
lean_dec(v_val_1541_);
lean_inc(v_defValue_1538_);
return v_defValue_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1543_, lean_object* v_opt_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1543_, v_opt_1544_);
lean_dec_ref(v_opt_1544_);
lean_dec_ref(v_opts_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1546_, size_t v_i_1547_, lean_object* v_bs_1548_){
_start:
{
uint8_t v___x_1549_; 
v___x_1549_ = lean_usize_dec_lt(v_i_1547_, v_sz_1546_);
if (v___x_1549_ == 0)
{
return v_bs_1548_;
}
else
{
lean_object* v_v_1550_; lean_object* v_msg_1551_; lean_object* v___x_1552_; lean_object* v_bs_x27_1553_; size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v_v_1550_ = lean_array_uget_borrowed(v_bs_1548_, v_i_1547_);
v_msg_1551_ = lean_ctor_get(v_v_1550_, 1);
lean_inc_ref(v_msg_1551_);
v___x_1552_ = lean_unsigned_to_nat(0u);
v_bs_x27_1553_ = lean_array_uset(v_bs_1548_, v_i_1547_, v___x_1552_);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1547_, v___x_1554_);
v___x_1556_ = lean_array_uset(v_bs_x27_1553_, v_i_1547_, v_msg_1551_);
v_i_1547_ = v___x_1555_;
v_bs_1548_ = v___x_1556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1558_, lean_object* v_i_1559_, lean_object* v_bs_1560_){
_start:
{
size_t v_sz_boxed_1561_; size_t v_i_boxed_1562_; lean_object* v_res_1563_; 
v_sz_boxed_1561_ = lean_unbox_usize(v_sz_1558_);
lean_dec(v_sz_1558_);
v_i_boxed_1562_ = lean_unbox_usize(v_i_1559_);
lean_dec(v_i_1559_);
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1561_, v_i_boxed_1562_, v_bs_1560_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1564_, lean_object* v_data_1565_, lean_object* v_ref_1566_, lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_toCold_1573_; lean_object* v_currRecDepth_1574_; lean_object* v_ref_1575_; uint8_t v_diag_1576_; uint8_t v_suppressElabErrors_1577_; lean_object* v_ref_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v_traceState_1581_; lean_object* v_traces_1582_; lean_object* v___x_1583_; size_t v_sz_1584_; size_t v___x_1585_; lean_object* v___x_1586_; lean_object* v_msg_1587_; lean_object* v___x_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1626_; 
v_toCold_1573_ = lean_ctor_get(v___y_1570_, 0);
v_currRecDepth_1574_ = lean_ctor_get(v___y_1570_, 1);
v_ref_1575_ = lean_ctor_get(v___y_1570_, 2);
v_diag_1576_ = lean_ctor_get_uint8(v___y_1570_, sizeof(void*)*3);
v_suppressElabErrors_1577_ = lean_ctor_get_uint8(v___y_1570_, sizeof(void*)*3 + 1);
v_ref_1578_ = l_Lean_replaceRef(v_ref_1566_, v_ref_1575_);
lean_inc(v_currRecDepth_1574_);
lean_inc_ref(v_toCold_1573_);
v___x_1579_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1579_, 0, v_toCold_1573_);
lean_ctor_set(v___x_1579_, 1, v_currRecDepth_1574_);
lean_ctor_set(v___x_1579_, 2, v_ref_1578_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3, v_diag_1576_);
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3 + 1, v_suppressElabErrors_1577_);
v___x_1580_ = lean_st_ref_get(v___y_1571_);
v_traceState_1581_ = lean_ctor_get(v___x_1580_, 4);
lean_inc_ref(v_traceState_1581_);
lean_dec(v___x_1580_);
v_traces_1582_ = lean_ctor_get(v_traceState_1581_, 0);
lean_inc_ref(v_traces_1582_);
lean_dec_ref(v_traceState_1581_);
v___x_1583_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1582_);
lean_dec_ref(v_traces_1582_);
v_sz_1584_ = lean_array_size(v___x_1583_);
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1584_, v___x_1585_, v___x_1583_);
v_msg_1587_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1587_, 0, v_data_1565_);
lean_ctor_set(v_msg_1587_, 1, v_msg_1567_);
lean_ctor_set(v_msg_1587_, 2, v___x_1586_);
v___x_1588_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1587_, v___y_1568_, v___y_1569_, v___x_1579_, v___y_1571_);
lean_dec_ref_known(v___x_1579_, 3);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1626_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1626_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v_traceState_1594_; lean_object* v_env_1595_; lean_object* v_nextMacroScope_1596_; lean_object* v_ngen_1597_; lean_object* v_auxDeclNGen_1598_; lean_object* v_cache_1599_; lean_object* v_messages_1600_; lean_object* v_infoState_1601_; lean_object* v_snapshotTasks_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1625_; 
v___x_1593_ = lean_st_ref_take(v___y_1571_);
v_traceState_1594_ = lean_ctor_get(v___x_1593_, 4);
v_env_1595_ = lean_ctor_get(v___x_1593_, 0);
v_nextMacroScope_1596_ = lean_ctor_get(v___x_1593_, 1);
v_ngen_1597_ = lean_ctor_get(v___x_1593_, 2);
v_auxDeclNGen_1598_ = lean_ctor_get(v___x_1593_, 3);
v_cache_1599_ = lean_ctor_get(v___x_1593_, 5);
v_messages_1600_ = lean_ctor_get(v___x_1593_, 6);
v_infoState_1601_ = lean_ctor_get(v___x_1593_, 7);
v_snapshotTasks_1602_ = lean_ctor_get(v___x_1593_, 8);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1604_ = v___x_1593_;
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_snapshotTasks_1602_);
lean_inc(v_infoState_1601_);
lean_inc(v_messages_1600_);
lean_inc(v_cache_1599_);
lean_inc(v_traceState_1594_);
lean_inc(v_auxDeclNGen_1598_);
lean_inc(v_ngen_1597_);
lean_inc(v_nextMacroScope_1596_);
lean_inc(v_env_1595_);
lean_dec(v___x_1593_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1625_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
uint64_t v_tid_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1623_; 
v_tid_1606_ = lean_ctor_get_uint64(v_traceState_1594_, sizeof(void*)*1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_traceState_1594_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; 
v_unused_1624_ = lean_ctor_get(v_traceState_1594_, 0);
lean_dec(v_unused_1624_);
v___x_1608_ = v_traceState_1594_;
v_isShared_1609_ = v_isSharedCheck_1623_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v_traceState_1594_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1623_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_ref_1566_);
lean_ctor_set(v___x_1611_, 1, v_a_1589_);
v___x_1612_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1564_, v___x_1611_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1612_);
v___x_1614_ = v___x_1608_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1612_);
lean_ctor_set_uint64(v_reuseFailAlloc_1622_, sizeof(void*)*1, v_tid_1606_);
v___x_1614_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 4, v___x_1614_);
v___x_1616_ = v___x_1604_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_env_1595_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_nextMacroScope_1596_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_ngen_1597_);
lean_ctor_set(v_reuseFailAlloc_1621_, 3, v_auxDeclNGen_1598_);
lean_ctor_set(v_reuseFailAlloc_1621_, 4, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1621_, 5, v_cache_1599_);
lean_ctor_set(v_reuseFailAlloc_1621_, 6, v_messages_1600_);
lean_ctor_set(v_reuseFailAlloc_1621_, 7, v_infoState_1601_);
lean_ctor_set(v_reuseFailAlloc_1621_, 8, v_snapshotTasks_1602_);
v___x_1616_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_st_ref_put(v___y_1571_, v___x_1616_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1610_);
v___x_1619_ = v___x_1591_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1610_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1627_, lean_object* v_data_1628_, lean_object* v_ref_1629_, lean_object* v_msg_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1627_, v_data_1628_, v_ref_1629_, v_msg_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1637_; double v___x_1638_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_float_of_nat(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1642_; double v___x_1643_; 
v___x_1642_ = lean_unsigned_to_nat(1000u);
v___x_1643_ = lean_float_of_nat(v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1644_, uint8_t v_collapsed_1645_, lean_object* v_tag_1646_, lean_object* v_opts_1647_, uint8_t v_clsEnabled_1648_, lean_object* v_oldTraces_1649_, lean_object* v_msg_1650_, lean_object* v_resStartStop_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_fst_1657_; lean_object* v_snd_1658_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v_data_1662_; lean_object* v_fst_1665_; lean_object* v_snd_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; lean_object* v___y_1670_; lean_object* v_a_1671_; uint8_t v___y_1686_; double v___y_1717_; 
v_fst_1657_ = lean_ctor_get(v_resStartStop_1651_, 0);
lean_inc(v_fst_1657_);
v_snd_1658_ = lean_ctor_get(v_resStartStop_1651_, 1);
lean_inc(v_snd_1658_);
lean_dec_ref(v_resStartStop_1651_);
v_fst_1665_ = lean_ctor_get(v_snd_1658_, 0);
lean_inc(v_fst_1665_);
v_snd_1666_ = lean_ctor_get(v_snd_1658_, 1);
lean_inc(v_snd_1666_);
lean_dec(v_snd_1658_);
v___x_1667_ = l_Lean_trace_profiler;
v___x_1668_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1647_, v___x_1667_);
if (v___x_1668_ == 0)
{
v___y_1686_ = v___x_1668_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1723_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1647_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; double v___x_1726_; double v___x_1727_; double v___x_1728_; 
v___x_1724_ = l_Lean_trace_profiler_threshold;
v___x_1725_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1647_, v___x_1724_);
v___x_1726_ = lean_float_of_nat(v___x_1725_);
v___x_1727_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1728_ = lean_float_div(v___x_1726_, v___x_1727_);
v___y_1717_ = v___x_1728_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; double v___x_1731_; 
v___x_1729_ = l_Lean_trace_profiler_threshold;
v___x_1730_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1647_, v___x_1729_);
v___x_1731_ = lean_float_of_nat(v___x_1730_);
v___y_1717_ = v___x_1731_;
goto v___jp_1716_;
}
}
v___jp_1659_:
{
lean_object* v___x_1663_; 
lean_inc(v___y_1660_);
v___x_1663_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1649_, v_data_1662_, v___y_1660_, v___y_1661_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; 
lean_dec_ref_known(v___x_1663_, 1);
v___x_1664_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1657_);
return v___x_1664_;
}
else
{
lean_dec(v_fst_1657_);
return v___x_1663_;
}
}
v___jp_1669_:
{
uint8_t v_result_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; double v___x_1675_; lean_object* v_data_1676_; 
v_result_1672_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1657_);
v___x_1673_ = lean_box(v_result_1672_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
v___x_1675_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1646_);
lean_inc_ref(v___x_1674_);
lean_inc(v_cls_1644_);
v_data_1676_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1676_, 0, v_cls_1644_);
lean_ctor_set(v_data_1676_, 1, v___x_1674_);
lean_ctor_set(v_data_1676_, 2, v_tag_1646_);
lean_ctor_set_float(v_data_1676_, sizeof(void*)*3, v___x_1675_);
lean_ctor_set_float(v_data_1676_, sizeof(void*)*3 + 8, v___x_1675_);
lean_ctor_set_uint8(v_data_1676_, sizeof(void*)*3 + 16, v_collapsed_1645_);
if (v___x_1668_ == 0)
{
lean_dec_ref_known(v___x_1674_, 1);
lean_dec(v_snd_1666_);
lean_dec(v_fst_1665_);
lean_dec_ref(v_tag_1646_);
lean_dec(v_cls_1644_);
v___y_1660_ = v___y_1670_;
v___y_1661_ = v_a_1671_;
v_data_1662_ = v_data_1676_;
goto v___jp_1659_;
}
else
{
lean_object* v_data_1677_; double v___x_1678_; double v___x_1679_; 
lean_dec_ref_known(v_data_1676_, 3);
v_data_1677_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1677_, 0, v_cls_1644_);
lean_ctor_set(v_data_1677_, 1, v___x_1674_);
lean_ctor_set(v_data_1677_, 2, v_tag_1646_);
v___x_1678_ = lean_unbox_float(v_fst_1665_);
lean_dec(v_fst_1665_);
lean_ctor_set_float(v_data_1677_, sizeof(void*)*3, v___x_1678_);
v___x_1679_ = lean_unbox_float(v_snd_1666_);
lean_dec(v_snd_1666_);
lean_ctor_set_float(v_data_1677_, sizeof(void*)*3 + 8, v___x_1679_);
lean_ctor_set_uint8(v_data_1677_, sizeof(void*)*3 + 16, v_collapsed_1645_);
v___y_1660_ = v___y_1670_;
v___y_1661_ = v_a_1671_;
v_data_1662_ = v_data_1677_;
goto v___jp_1659_;
}
}
v___jp_1680_:
{
lean_object* v_ref_1681_; lean_object* v___x_1682_; 
v_ref_1681_ = lean_ctor_get(v___y_1654_, 2);
lean_inc(v___y_1655_);
lean_inc_ref(v___y_1654_);
lean_inc(v___y_1653_);
lean_inc_ref(v___y_1652_);
lean_inc(v_fst_1657_);
v___x_1682_ = lean_apply_6(v_msg_1650_, v_fst_1657_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, lean_box(0));
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v___y_1670_ = v_ref_1681_;
v_a_1671_ = v_a_1683_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1684_; 
lean_dec_ref_known(v___x_1682_, 1);
v___x_1684_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1670_ = v_ref_1681_;
v_a_1671_ = v___x_1684_;
goto v___jp_1669_;
}
}
v___jp_1685_:
{
if (v_clsEnabled_1648_ == 0)
{
if (v___y_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v_traceState_1688_; lean_object* v_env_1689_; lean_object* v_nextMacroScope_1690_; lean_object* v_ngen_1691_; lean_object* v_auxDeclNGen_1692_; lean_object* v_cache_1693_; lean_object* v_messages_1694_; lean_object* v_infoState_1695_; lean_object* v_snapshotTasks_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_snd_1666_);
lean_dec(v_fst_1665_);
lean_dec_ref(v_msg_1650_);
lean_dec_ref(v_tag_1646_);
lean_dec(v_cls_1644_);
v___x_1687_ = lean_st_ref_take(v___y_1655_);
v_traceState_1688_ = lean_ctor_get(v___x_1687_, 4);
v_env_1689_ = lean_ctor_get(v___x_1687_, 0);
v_nextMacroScope_1690_ = lean_ctor_get(v___x_1687_, 1);
v_ngen_1691_ = lean_ctor_get(v___x_1687_, 2);
v_auxDeclNGen_1692_ = lean_ctor_get(v___x_1687_, 3);
v_cache_1693_ = lean_ctor_get(v___x_1687_, 5);
v_messages_1694_ = lean_ctor_get(v___x_1687_, 6);
v_infoState_1695_ = lean_ctor_get(v___x_1687_, 7);
v_snapshotTasks_1696_ = lean_ctor_get(v___x_1687_, 8);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1698_ = v___x_1687_;
v_isShared_1699_ = v_isSharedCheck_1715_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snapshotTasks_1696_);
lean_inc(v_infoState_1695_);
lean_inc(v_messages_1694_);
lean_inc(v_cache_1693_);
lean_inc(v_traceState_1688_);
lean_inc(v_auxDeclNGen_1692_);
lean_inc(v_ngen_1691_);
lean_inc(v_nextMacroScope_1690_);
lean_inc(v_env_1689_);
lean_dec(v___x_1687_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1715_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
uint64_t v_tid_1700_; lean_object* v_traces_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1714_; 
v_tid_1700_ = lean_ctor_get_uint64(v_traceState_1688_, sizeof(void*)*1);
v_traces_1701_ = lean_ctor_get(v_traceState_1688_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_traceState_1688_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1703_ = v_traceState_1688_;
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_traces_1701_);
lean_dec(v_traceState_1688_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1649_, v_traces_1701_);
lean_dec_ref(v_traces_1701_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1705_);
lean_ctor_set_uint64(v_reuseFailAlloc_1713_, sizeof(void*)*1, v_tid_1700_);
v___x_1707_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 4, v___x_1707_);
v___x_1709_ = v___x_1698_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_env_1689_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_nextMacroScope_1690_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_ngen_1691_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_auxDeclNGen_1692_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_cache_1693_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_messages_1694_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_infoState_1695_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_snapshotTasks_1696_);
v___x_1709_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = lean_st_ref_put(v___y_1655_, v___x_1709_);
v___x_1711_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1657_);
return v___x_1711_;
}
}
}
}
}
else
{
goto v___jp_1680_;
}
}
else
{
goto v___jp_1680_;
}
}
v___jp_1716_:
{
double v___x_1718_; double v___x_1719_; double v___x_1720_; uint8_t v___x_1721_; 
v___x_1718_ = lean_unbox_float(v_snd_1666_);
v___x_1719_ = lean_unbox_float(v_fst_1665_);
v___x_1720_ = lean_float_sub(v___x_1718_, v___x_1719_);
v___x_1721_ = lean_float_decLt(v___y_1717_, v___x_1720_);
v___y_1686_ = v___x_1721_;
goto v___jp_1685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1732_, lean_object* v_collapsed_1733_, lean_object* v_tag_1734_, lean_object* v_opts_1735_, lean_object* v_clsEnabled_1736_, lean_object* v_oldTraces_1737_, lean_object* v_msg_1738_, lean_object* v_resStartStop_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
uint8_t v_collapsed_boxed_1745_; uint8_t v_clsEnabled_boxed_1746_; lean_object* v_res_1747_; 
v_collapsed_boxed_1745_ = lean_unbox(v_collapsed_1733_);
v_clsEnabled_boxed_1746_ = lean_unbox(v_clsEnabled_1736_);
v_res_1747_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1732_, v_collapsed_boxed_1745_, v_tag_1734_, v_opts_1735_, v_clsEnabled_boxed_1746_, v_oldTraces_1737_, v_msg_1738_, v_resStartStop_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_opts_1735_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1748_, lean_object* v___x_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v_a_1752_, lean_object* v_b_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_nat_dec_lt(v_a_1752_, v_upperBound_1748_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec(v_a_1752_);
lean_dec(v___x_1751_);
lean_dec(v___x_1750_);
lean_dec(v___x_1749_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_b_1753_);
return v___x_1760_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_a_1752_, v___x_1762_);
lean_dec(v_a_1752_);
lean_inc_n(v___x_1763_, 2);
lean_inc(v___x_1749_);
v___x_1764_ = lean_name_append_index_after(v___x_1749_, v___x_1763_);
lean_inc(v___x_1750_);
v___x_1765_ = lean_name_append_index_after(v___x_1750_, v___x_1763_);
lean_inc(v___x_1751_);
v___x_1766_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1764_, v___x_1751_, v___x_1765_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_dec_ref_known(v___x_1766_, 1);
v_a_1752_ = v___x_1763_;
v_b_1753_ = v___x_1761_;
goto _start;
}
else
{
lean_dec(v___x_1763_);
lean_dec(v___x_1751_);
lean_dec(v___x_1750_);
lean_dec(v___x_1749_);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1768_, lean_object* v___x_1769_, lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v_a_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1768_, v___x_1769_, v___x_1770_, v___x_1771_, v_a_1772_, v_b_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v_upperBound_1768_);
return v_res_1779_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1789_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1790_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1791_ = l_Lean_Name_append(v___x_1790_, v___x_1789_);
return v___x_1791_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1792_; double v___x_1793_; 
v___x_1792_ = lean_unsigned_to_nat(1000000000u);
v___x_1793_ = lean_float_of_nat(v___x_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_toCold_1800_; lean_object* v_options_1801_; lean_object* v_inheritedTraceOptions_1802_; uint8_t v_hasTrace_1803_; lean_object* v___x_1804_; 
v_toCold_1800_ = lean_ctor_get(v_a_1797_, 0);
v_options_1801_ = lean_ctor_get(v_toCold_1800_, 2);
v_inheritedTraceOptions_1802_ = lean_ctor_get(v_toCold_1800_, 11);
v_hasTrace_1803_ = lean_ctor_get_uint8(v_options_1801_, sizeof(void*)*1);
v___x_1804_ = lean_box(0);
if (v_hasTrace_1803_ == 0)
{
lean_object* v___x_1805_; 
lean_inc(v_indName_1794_);
v___x_1805_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1869_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1869_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1869_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
if (lean_obj_tag(v_a_1806_) == 5)
{
lean_object* v_val_1810_; uint8_t v_isRec_1811_; 
v_val_1810_ = lean_ctor_get(v_a_1806_, 0);
lean_inc_ref(v_val_1810_);
lean_dec_ref_known(v_a_1806_, 1);
v_isRec_1811_ = lean_ctor_get_uint8(v_val_1810_, sizeof(void*)*6);
if (v_isRec_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec_ref(v_val_1810_);
lean_dec(v_indName_1794_);
v___x_1812_ = lean_box(0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1812_);
v___x_1814_ = v___x_1808_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v_toConstantVal_1816_; lean_object* v_numParams_1817_; lean_object* v_all_1818_; lean_object* v_numNested_1819_; lean_object* v_type_1820_; lean_object* v___x_1821_; 
lean_del_object(v___x_1808_);
v_toConstantVal_1816_ = lean_ctor_get(v_val_1810_, 0);
lean_inc_ref(v_toConstantVal_1816_);
v_numParams_1817_ = lean_ctor_get(v_val_1810_, 1);
lean_inc(v_numParams_1817_);
v_all_1818_ = lean_ctor_get(v_val_1810_, 3);
lean_inc(v_all_1818_);
v_numNested_1819_ = lean_ctor_get(v_val_1810_, 5);
lean_inc(v_numNested_1819_);
lean_dec_ref(v_val_1810_);
v_type_1820_ = lean_ctor_get(v_toConstantVal_1816_, 2);
lean_inc_ref(v_type_1820_);
lean_dec_ref(v_toConstantVal_1816_);
v___x_1821_ = l_Lean_Meta_isPropFormerType(v_type_1820_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1856_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1856_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1856_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_unbox(v_a_1822_);
lean_dec(v_a_1822_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_del_object(v___x_1824_);
lean_inc_n(v_indName_1794_, 2);
v___x_1827_ = l_Lean_mkRecName(v_indName_1794_);
v___x_1828_ = l_Lean_mkBelowName(v_indName_1794_);
lean_inc(v___x_1828_);
lean_inc(v_numParams_1817_);
lean_inc(v___x_1827_);
v___x_1829_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1827_, v_numParams_1817_, v___x_1828_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1850_; 
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1851_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1850_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1850_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = l_List_get_x21Internal___redArg(v___x_1804_, v_all_1818_, v___x_1833_);
lean_dec(v_all_1818_);
v___x_1835_ = lean_name_eq(v___x_1834_, v_indName_1794_);
lean_dec(v_indName_1794_);
lean_dec(v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec(v___x_1828_);
lean_dec(v___x_1827_);
lean_dec(v_numNested_1819_);
lean_dec(v_numParams_1817_);
v___x_1836_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1836_);
v___x_1838_ = v___x_1831_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
lean_del_object(v___x_1831_);
v___x_1840_ = lean_box(0);
v___x_1841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1819_, v___x_1827_, v___x_1828_, v_numParams_1817_, v___x_1833_, v___x_1840_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_numNested_1819_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1849_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1840_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1840_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
return v___x_1841_;
}
}
}
}
else
{
lean_dec(v___x_1828_);
lean_dec(v___x_1827_);
lean_dec(v_numNested_1819_);
lean_dec(v_all_1818_);
lean_dec(v_numParams_1817_);
lean_dec(v_indName_1794_);
return v___x_1829_;
}
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec(v_numNested_1819_);
lean_dec(v_all_1818_);
lean_dec(v_numParams_1817_);
lean_dec(v_indName_1794_);
v___x_1852_ = lean_box(0);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1852_);
v___x_1854_ = v___x_1824_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_numNested_1819_);
lean_dec(v_all_1818_);
lean_dec(v_numParams_1817_);
lean_dec(v_indName_1794_);
v_a_1857_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1821_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1821_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_a_1806_);
lean_dec(v_indName_1794_);
v___x_1865_ = lean_box(0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1865_);
v___x_1867_ = v___x_1808_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_indName_1794_);
v_a_1870_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1805_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1805_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
else
{
lean_object* v___f_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_a_1886_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v_a_1901_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v_a_1906_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v_a_1911_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v_a_1923_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v_a_1928_; 
lean_inc(v_indName_1794_);
v___f_1878_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1878_, 0, v_indName_1794_);
v___x_1879_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1880_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1881_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1802_, v_options_1801_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = l_Lean_trace_profiler;
v___x_1996_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1801_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec_ref(v___f_1878_);
lean_inc(v_indName_1794_);
v___x_1997_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2061_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2061_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2061_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
if (lean_obj_tag(v_a_1998_) == 5)
{
lean_object* v_val_2002_; uint8_t v_isRec_2003_; 
v_val_2002_ = lean_ctor_get(v_a_1998_, 0);
lean_inc_ref(v_val_2002_);
lean_dec_ref_known(v_a_1998_, 1);
v_isRec_2003_ = lean_ctor_get_uint8(v_val_2002_, sizeof(void*)*6);
if (v_isRec_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_dec_ref(v_val_2002_);
lean_dec(v_indName_1794_);
v___x_2004_ = lean_box(0);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2004_);
v___x_2006_ = v___x_2000_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v_toConstantVal_2008_; lean_object* v_numParams_2009_; lean_object* v_all_2010_; lean_object* v_numNested_2011_; lean_object* v_type_2012_; lean_object* v___x_2013_; 
lean_del_object(v___x_2000_);
v_toConstantVal_2008_ = lean_ctor_get(v_val_2002_, 0);
lean_inc_ref(v_toConstantVal_2008_);
v_numParams_2009_ = lean_ctor_get(v_val_2002_, 1);
lean_inc(v_numParams_2009_);
v_all_2010_ = lean_ctor_get(v_val_2002_, 3);
lean_inc(v_all_2010_);
v_numNested_2011_ = lean_ctor_get(v_val_2002_, 5);
lean_inc(v_numNested_2011_);
lean_dec_ref(v_val_2002_);
v_type_2012_ = lean_ctor_get(v_toConstantVal_2008_, 2);
lean_inc_ref(v_type_2012_);
lean_dec_ref(v_toConstantVal_2008_);
v___x_2013_ = l_Lean_Meta_isPropFormerType(v_type_2012_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2048_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2048_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2048_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_unbox(v_a_2014_);
lean_dec(v_a_2014_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
lean_del_object(v___x_2016_);
lean_inc_n(v_indName_1794_, 2);
v___x_2019_ = l_Lean_mkRecName(v_indName_1794_);
v___x_2020_ = l_Lean_mkBelowName(v_indName_1794_);
lean_inc(v___x_2020_);
lean_inc(v_numParams_2009_);
lean_inc(v___x_2019_);
v___x_2021_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2019_, v_numParams_2009_, v___x_2020_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2042_; 
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2043_);
v___x_2023_ = v___x_2021_;
v_isShared_2024_ = v_isSharedCheck_2042_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v___x_2021_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2042_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = l_List_get_x21Internal___redArg(v___x_1804_, v_all_2010_, v___x_2025_);
lean_dec(v_all_2010_);
v___x_2027_ = lean_name_eq(v___x_2026_, v_indName_1794_);
lean_dec(v_indName_1794_);
lean_dec(v___x_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v___x_2020_);
lean_dec(v___x_2019_);
lean_dec(v_numNested_2011_);
lean_dec(v_numParams_2009_);
v___x_2028_ = lean_box(0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2028_);
v___x_2030_ = v___x_2023_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_del_object(v___x_2023_);
v___x_2032_ = lean_box(0);
v___x_2033_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2011_, v___x_2019_, v___x_2020_, v_numParams_2009_, v___x_2025_, v___x_2032_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_numNested_2011_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2041_);
v___x_2035_ = v___x_2033_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2033_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2032_);
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2032_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
return v___x_2033_;
}
}
}
}
else
{
lean_dec(v___x_2020_);
lean_dec(v___x_2019_);
lean_dec(v_numNested_2011_);
lean_dec(v_all_2010_);
lean_dec(v_numParams_2009_);
lean_dec(v_indName_1794_);
return v___x_2021_;
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
lean_dec(v_numNested_2011_);
lean_dec(v_all_2010_);
lean_dec(v_numParams_2009_);
lean_dec(v_indName_1794_);
v___x_2044_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2044_);
v___x_2046_ = v___x_2016_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_numNested_2011_);
lean_dec(v_all_2010_);
lean_dec(v_numParams_2009_);
lean_dec(v_indName_1794_);
v_a_2049_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2013_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2013_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
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
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v_a_1998_);
lean_dec(v_indName_1794_);
v___x_2057_ = lean_box(0);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2057_);
v___x_2059_ = v___x_2000_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_indName_1794_);
v_a_2062_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1997_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1997_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
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
goto v___jp_1930_;
}
}
else
{
goto v___jp_1930_;
}
v___jp_1883_:
{
lean_object* v___x_1887_; double v___x_1888_; double v___x_1889_; double v___x_1890_; double v___x_1891_; double v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1887_ = lean_io_mono_nanos_now();
v___x_1888_ = lean_float_of_nat(v___y_1885_);
v___x_1889_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1890_ = lean_float_div(v___x_1888_, v___x_1889_);
v___x_1891_ = lean_float_of_nat(v___x_1887_);
v___x_1892_ = lean_float_div(v___x_1891_, v___x_1889_);
v___x_1893_ = lean_box_float(v___x_1890_);
v___x_1894_ = lean_box_float(v___x_1892_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_a_1886_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1879_, v_hasTrace_1803_, v___x_1880_, v_options_1801_, v___x_1882_, v___y_1884_, v___f_1878_, v___x_1896_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1897_;
}
v___jp_1898_:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v_a_1901_);
v___y_1884_ = v___y_1899_;
v___y_1885_ = v___y_1900_;
v_a_1886_ = v___x_1902_;
goto v___jp_1883_;
}
v___jp_1903_:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1906_);
v___y_1884_ = v___y_1904_;
v___y_1885_ = v___y_1905_;
v_a_1886_ = v___x_1907_;
goto v___jp_1883_;
}
v___jp_1908_:
{
lean_object* v___x_1912_; double v___x_1913_; double v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1912_ = lean_io_get_num_heartbeats();
v___x_1913_ = lean_float_of_nat(v___y_1909_);
v___x_1914_ = lean_float_of_nat(v___x_1912_);
v___x_1915_ = lean_box_float(v___x_1913_);
v___x_1916_ = lean_box_float(v___x_1914_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_a_1911_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1879_, v_hasTrace_1803_, v___x_1880_, v_options_1801_, v___x_1882_, v___y_1910_, v___f_1878_, v___x_1918_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1919_;
}
v___jp_1920_:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_a_1923_);
v___y_1909_ = v___y_1921_;
v___y_1910_ = v___y_1922_;
v_a_1911_ = v___x_1924_;
goto v___jp_1908_;
}
v___jp_1925_:
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_a_1928_);
v___y_1909_ = v___y_1926_;
v___y_1910_ = v___y_1927_;
v_a_1911_ = v___x_1929_;
goto v___jp_1908_;
}
v___jp_1930_:
{
lean_object* v___x_1931_; lean_object* v_a_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1931_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1798_);
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
v___x_1933_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1934_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1801_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1794_);
v___x_1936_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
if (lean_obj_tag(v_a_1937_) == 5)
{
lean_object* v_val_1938_; uint8_t v_isRec_1939_; 
v_val_1938_ = lean_ctor_get(v_a_1937_, 0);
lean_inc_ref(v_val_1938_);
lean_dec_ref_known(v_a_1937_, 1);
v_isRec_1939_ = lean_ctor_get_uint8(v_val_1938_, sizeof(void*)*6);
if (v_isRec_1939_ == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref(v_val_1938_);
lean_dec(v_indName_1794_);
v___x_1940_ = lean_box(0);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v___x_1940_;
goto v___jp_1898_;
}
else
{
lean_object* v_toConstantVal_1941_; lean_object* v_numParams_1942_; lean_object* v_all_1943_; lean_object* v_numNested_1944_; lean_object* v_type_1945_; lean_object* v___x_1946_; 
v_toConstantVal_1941_ = lean_ctor_get(v_val_1938_, 0);
lean_inc_ref(v_toConstantVal_1941_);
v_numParams_1942_ = lean_ctor_get(v_val_1938_, 1);
lean_inc(v_numParams_1942_);
v_all_1943_ = lean_ctor_get(v_val_1938_, 3);
lean_inc(v_all_1943_);
v_numNested_1944_ = lean_ctor_get(v_val_1938_, 5);
lean_inc(v_numNested_1944_);
lean_dec_ref(v_val_1938_);
v_type_1945_ = lean_ctor_get(v_toConstantVal_1941_, 2);
lean_inc_ref(v_type_1945_);
lean_dec_ref(v_toConstantVal_1941_);
v___x_1946_ = l_Lean_Meta_isPropFormerType(v_type_1945_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_inc_n(v_indName_1794_, 2);
v___x_1949_ = l_Lean_mkRecName(v_indName_1794_);
v___x_1950_ = l_Lean_mkBelowName(v_indName_1794_);
lean_inc(v___x_1950_);
lean_inc(v_numParams_1942_);
lean_inc(v___x_1949_);
v___x_1951_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1949_, v_numParams_1942_, v___x_1950_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
lean_dec_ref_known(v___x_1951_, 1);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = l_List_get_x21Internal___redArg(v___x_1804_, v_all_1943_, v___x_1952_);
lean_dec(v_all_1943_);
v___x_1954_ = lean_name_eq(v___x_1953_, v_indName_1794_);
lean_dec(v_indName_1794_);
lean_dec(v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v___x_1955_; 
lean_dec(v___x_1950_);
lean_dec(v___x_1949_);
lean_dec(v_numNested_1944_);
lean_dec(v_numParams_1942_);
v___x_1955_ = lean_box(0);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v___x_1955_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1944_, v___x_1949_, v___x_1950_, v_numParams_1942_, v___x_1952_, v___x_1956_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_numNested_1944_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_dec_ref_known(v___x_1957_, 1);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v___x_1956_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___y_1904_ = v_a_1932_;
v___y_1905_ = v___x_1935_;
v_a_1906_ = v_a_1958_;
goto v___jp_1903_;
}
}
}
else
{
lean_dec(v___x_1950_);
lean_dec(v___x_1949_);
lean_dec(v_numNested_1944_);
lean_dec(v_all_1943_);
lean_dec(v_numParams_1942_);
lean_dec(v_indName_1794_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1951_, 1);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v_a_1959_;
goto v___jp_1898_;
}
else
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1951_, 1);
v___y_1904_ = v_a_1932_;
v___y_1905_ = v___x_1935_;
v_a_1906_ = v_a_1960_;
goto v___jp_1903_;
}
}
}
else
{
lean_object* v___x_1961_; 
lean_dec(v_numNested_1944_);
lean_dec(v_all_1943_);
lean_dec(v_numParams_1942_);
lean_dec(v_indName_1794_);
v___x_1961_ = lean_box(0);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v___x_1961_;
goto v___jp_1898_;
}
}
else
{
lean_object* v_a_1962_; 
lean_dec(v_numNested_1944_);
lean_dec(v_all_1943_);
lean_dec(v_numParams_1942_);
lean_dec(v_indName_1794_);
v_a_1962_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1946_, 1);
v___y_1904_ = v_a_1932_;
v___y_1905_ = v___x_1935_;
v_a_1906_ = v_a_1962_;
goto v___jp_1903_;
}
}
}
else
{
lean_object* v___x_1963_; 
lean_dec(v_a_1937_);
lean_dec(v_indName_1794_);
v___x_1963_ = lean_box(0);
v___y_1899_ = v_a_1932_;
v___y_1900_ = v___x_1935_;
v_a_1901_ = v___x_1963_;
goto v___jp_1898_;
}
}
else
{
lean_object* v_a_1964_; 
lean_dec(v_indName_1794_);
v_a_1964_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1936_, 1);
v___y_1904_ = v_a_1932_;
v___y_1905_ = v___x_1935_;
v_a_1906_ = v_a_1964_;
goto v___jp_1903_;
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1794_);
v___x_1966_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1966_, 1);
if (lean_obj_tag(v_a_1967_) == 5)
{
lean_object* v_val_1968_; uint8_t v_isRec_1969_; 
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc_ref(v_val_1968_);
lean_dec_ref_known(v_a_1967_, 1);
v_isRec_1969_ = lean_ctor_get_uint8(v_val_1968_, sizeof(void*)*6);
if (v_isRec_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec_ref(v_val_1968_);
lean_dec(v_indName_1794_);
v___x_1970_ = lean_box(0);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v___x_1970_;
goto v___jp_1920_;
}
else
{
lean_object* v_toConstantVal_1971_; lean_object* v_numParams_1972_; lean_object* v_all_1973_; lean_object* v_numNested_1974_; lean_object* v_type_1975_; lean_object* v___x_1976_; 
v_toConstantVal_1971_ = lean_ctor_get(v_val_1968_, 0);
lean_inc_ref(v_toConstantVal_1971_);
v_numParams_1972_ = lean_ctor_get(v_val_1968_, 1);
lean_inc(v_numParams_1972_);
v_all_1973_ = lean_ctor_get(v_val_1968_, 3);
lean_inc(v_all_1973_);
v_numNested_1974_ = lean_ctor_get(v_val_1968_, 5);
lean_inc(v_numNested_1974_);
lean_dec_ref(v_val_1968_);
v_type_1975_ = lean_ctor_get(v_toConstantVal_1971_, 2);
lean_inc_ref(v_type_1975_);
lean_dec_ref(v_toConstantVal_1971_);
v___x_1976_ = l_Lean_Meta_isPropFormerType(v_type_1975_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1976_, 1);
v___x_1978_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_inc_n(v_indName_1794_, 2);
v___x_1979_ = l_Lean_mkRecName(v_indName_1794_);
v___x_1980_ = l_Lean_mkBelowName(v_indName_1794_);
lean_inc(v___x_1980_);
lean_inc(v_numParams_1972_);
lean_inc(v___x_1979_);
v___x_1981_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1979_, v_numParams_1972_, v___x_1980_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
lean_dec_ref_known(v___x_1981_, 1);
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = l_List_get_x21Internal___redArg(v___x_1804_, v_all_1973_, v___x_1982_);
lean_dec(v_all_1973_);
v___x_1984_ = lean_name_eq(v___x_1983_, v_indName_1794_);
lean_dec(v_indName_1794_);
lean_dec(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec(v___x_1980_);
lean_dec(v___x_1979_);
lean_dec(v_numNested_1974_);
lean_dec(v_numParams_1972_);
v___x_1985_ = lean_box(0);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v___x_1985_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1974_, v___x_1979_, v___x_1980_, v_numParams_1972_, v___x_1982_, v___x_1986_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
lean_dec(v_numNested_1974_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_dec_ref_known(v___x_1987_, 1);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v___x_1986_;
goto v___jp_1920_;
}
else
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___y_1926_ = v___x_1965_;
v___y_1927_ = v_a_1932_;
v_a_1928_ = v_a_1988_;
goto v___jp_1925_;
}
}
}
else
{
lean_dec(v___x_1980_);
lean_dec(v___x_1979_);
lean_dec(v_numNested_1974_);
lean_dec(v_all_1973_);
lean_dec(v_numParams_1972_);
lean_dec(v_indName_1794_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1981_, 1);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v_a_1989_;
goto v___jp_1920_;
}
else
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1981_, 1);
v___y_1926_ = v___x_1965_;
v___y_1927_ = v_a_1932_;
v_a_1928_ = v_a_1990_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_numNested_1974_);
lean_dec(v_all_1973_);
lean_dec(v_numParams_1972_);
lean_dec(v_indName_1794_);
v___x_1991_ = lean_box(0);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v___x_1991_;
goto v___jp_1920_;
}
}
else
{
lean_object* v_a_1992_; 
lean_dec(v_numNested_1974_);
lean_dec(v_all_1973_);
lean_dec(v_numParams_1972_);
lean_dec(v_indName_1794_);
v_a_1992_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1992_);
lean_dec_ref_known(v___x_1976_, 1);
v___y_1926_ = v___x_1965_;
v___y_1927_ = v_a_1932_;
v_a_1928_ = v_a_1992_;
goto v___jp_1925_;
}
}
}
else
{
lean_object* v___x_1993_; 
lean_dec(v_a_1967_);
lean_dec(v_indName_1794_);
v___x_1993_ = lean_box(0);
v___y_1921_ = v___x_1965_;
v___y_1922_ = v_a_1932_;
v_a_1923_ = v___x_1993_;
goto v___jp_1920_;
}
}
else
{
lean_object* v_a_1994_; 
lean_dec(v_indName_1794_);
v_a_1994_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1966_, 1);
v___y_1926_ = v___x_1965_;
v___y_1927_ = v_a_1932_;
v_a_1928_ = v_a_1994_;
goto v___jp_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_mkBelow(v_indName_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2077_, lean_object* v___x_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v_inst_2081_, lean_object* v_R_2082_, lean_object* v_a_2083_, lean_object* v_b_2084_, lean_object* v_c_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2077_, v___x_2078_, v___x_2079_, v___x_2080_, v_a_2083_, v_b_2084_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v_inst_2096_, lean_object* v_R_2097_, lean_object* v_a_2098_, lean_object* v_b_2099_, lean_object* v_c_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2092_, v___x_2093_, v___x_2094_, v___x_2095_, v_inst_2096_, v_R_2097_, v_a_2098_, v_b_2099_, v_c_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_upperBound_2092_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2107_, lean_object* v_x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2108_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2115_, lean_object* v_x_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2115_, v_x_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
if (lean_obj_tag(v_a_2123_) == 0)
{
lean_object* v___x_2125_; 
v___x_2125_ = l_List_reverse___redArg(v_a_2124_);
return v___x_2125_;
}
else
{
lean_object* v_head_2126_; lean_object* v_tail_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2136_; 
v_head_2126_ = lean_ctor_get(v_a_2123_, 0);
v_tail_2127_ = lean_ctor_get(v_a_2123_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_a_2123_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2129_ = v_a_2123_;
v_isShared_2130_ = v_isSharedCheck_2136_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_tail_2127_);
lean_inc(v_head_2126_);
lean_dec(v_a_2123_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2136_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2131_ = l_Lean_MessageData_ofExpr(v_head_2126_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 1, v_a_2124_);
lean_ctor_set(v___x_2129_, 0, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_a_2124_);
v___x_2133_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
v_a_2123_ = v_tail_2127_;
v_a_2124_ = v___x_2133_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2137_, lean_object* v_v_2138_, lean_object* v_i_2139_){
_start:
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = lean_array_get_size(v_xs_2137_);
v___x_2141_ = lean_nat_dec_lt(v_i_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; 
lean_dec(v_i_2139_);
v___x_2142_ = lean_box(0);
return v___x_2142_;
}
else
{
lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2143_ = lean_array_fget_borrowed(v_xs_2137_, v_i_2139_);
v___x_2144_ = lean_expr_eqv(v___x_2143_, v_v_2138_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_i_2139_, v___x_2145_);
lean_dec(v_i_2139_);
v_i_2139_ = v___x_2146_;
goto _start;
}
else
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_i_2139_);
return v___x_2148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2149_, lean_object* v_v_2150_, lean_object* v_i_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2149_, v_v_2150_, v_i_2151_);
lean_dec_ref(v_v_2150_);
lean_dec_ref(v_xs_2149_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2153_, lean_object* v_v_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2153_, v_v_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2157_, lean_object* v_v_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2157_, v_v_2158_);
lean_dec_ref(v_v_2158_);
lean_dec_ref(v_xs_2157_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2160_, lean_object* v_v_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2160_, v_v_2161_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
else
{
lean_object* v_val_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_val_2164_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2162_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_val_2164_);
lean_dec(v___x_2162_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_val_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2172_, lean_object* v_v_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2172_, v_v_2173_);
lean_dec_ref(v_v_2173_);
lean_dec_ref(v_xs_2172_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2177_ = l_Lean_stringToMessageData(v___x_2176_);
return v___x_2177_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2180_ = l_Lean_stringToMessageData(v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2181_, lean_object* v_prods_2182_, lean_object* v_motives_2183_, lean_object* v_fs_2184_, lean_object* v_minor__type_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 5)
{
lean_object* v_fn_2194_; lean_object* v_arg_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v_fn_2194_ = lean_ctor_get(v_x_2186_, 0);
lean_inc_ref(v_fn_2194_);
v_arg_2195_ = lean_ctor_get(v_x_2186_, 1);
lean_inc_ref(v_arg_2195_);
lean_dec_ref_known(v_x_2186_, 2);
v___x_2196_ = lean_array_set(v_x_2187_, v_x_2188_, v_arg_2195_);
v___x_2197_ = lean_unsigned_to_nat(1u);
v___x_2198_ = lean_nat_sub(v_x_2188_, v___x_2197_);
lean_dec(v_x_2188_);
v_x_2186_ = v_fn_2194_;
v_x_2187_ = v___x_2196_;
v_x_2188_ = v___x_2198_;
goto _start;
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
lean_dec(v_x_2188_);
v___x_2200_ = l_Lean_instInhabitedExpr;
v___x_2201_ = l_Lean_Meta_PProdN_mk(v_rlvl_2181_, v_prods_2182_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2183_, v_x_2186_);
lean_dec_ref(v_x_2186_);
if (lean_obj_tag(v___x_2203_) == 1)
{
lean_object* v_val_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_minor__type_2185_);
lean_dec_ref(v_motives_2183_);
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = lean_array_get_borrowed(v___x_2200_, v_fs_2184_, v_val_2204_);
lean_dec(v_val_2204_);
lean_inc(v_a_2202_);
v___x_2206_ = lean_array_push(v_x_2187_, v_a_2202_);
lean_inc(v___x_2205_);
v___x_2207_ = l_Lean_mkAppN(v___x_2205_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = l_Lean_Meta_mkPProdMk(v___x_2207_, v_a_2202_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v___x_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_x_2187_);
v___x_2209_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2210_ = l_Lean_MessageData_ofExpr(v_minor__type_2185_);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = lean_array_to_list(v_motives_2183_);
v___x_2215_ = lean_box(0);
v___x_2216_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2214_, v___x_2215_);
v___x_2217_ = l_Lean_MessageData_ofList(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2213_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2218_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2219_;
}
}
else
{
lean_dec_ref(v_x_2187_);
lean_dec_ref(v_x_2186_);
lean_dec_ref(v_minor__type_2185_);
lean_dec_ref(v_motives_2183_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2220_, lean_object* v_prods_2221_, lean_object* v_motives_2222_, lean_object* v_fs_2223_, lean_object* v_minor__type_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2220_, v_prods_2221_, v_motives_2222_, v_fs_2223_, v_minor__type_2224_, v_x_2225_, v_x_2226_, v_x_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_fs_2223_);
return v_res_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2234_; lean_object* v_dummy_2235_; 
v___x_2234_ = lean_box(0);
v_dummy_2235_ = l_Lean_Expr_sort___override(v___x_2234_);
return v_dummy_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2236_, lean_object* v_head_2237_, lean_object* v_belows_2238_, lean_object* v_prods_2239_, lean_object* v_rlvl_2240_, lean_object* v_fs_2241_, lean_object* v_minor__type_2242_, lean_object* v_tail_2243_, lean_object* v_arg__args_2244_, lean_object* v_arg__type_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2236_, v_head_2237_, v_belows_2238_, v_prods_2239_, v_rlvl_2240_, v_fs_2241_, v_minor__type_2242_, v_tail_2243_, v_arg__args_2244_, v_arg__type_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec_ref(v_arg__args_2244_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2252_, lean_object* v_motives_2253_, lean_object* v_belows_2254_, lean_object* v_fs_2255_, lean_object* v_minor__type_2256_, lean_object* v_prods_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
if (lean_obj_tag(v_a_2258_) == 0)
{
lean_object* v_dummy_2264_; lean_object* v_nargs_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
lean_dec_ref(v_belows_2254_);
v_dummy_2264_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2265_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2256_);
lean_inc(v_nargs_2265_);
v___x_2266_ = lean_mk_array(v_nargs_2265_, v_dummy_2264_);
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_sub(v_nargs_2265_, v___x_2267_);
lean_dec(v_nargs_2265_);
lean_inc_ref(v_minor__type_2256_);
v___x_2269_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2252_, v_prods_2257_, v_motives_2253_, v_fs_2255_, v_minor__type_2256_, v_minor__type_2256_, v___x_2266_, v___x_2268_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec_ref(v_fs_2255_);
return v___x_2269_;
}
else
{
lean_object* v_head_2270_; lean_object* v_tail_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v_head_2270_ = lean_ctor_get(v_a_2258_, 0);
lean_inc_n(v_head_2270_, 2);
v_tail_2271_ = lean_ctor_get(v_a_2258_, 1);
lean_inc(v_tail_2271_);
lean_dec_ref_known(v_a_2258_, 2);
v___f_2272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2272_, 0, v_motives_2253_);
lean_closure_set(v___f_2272_, 1, v_head_2270_);
lean_closure_set(v___f_2272_, 2, v_belows_2254_);
lean_closure_set(v___f_2272_, 3, v_prods_2257_);
lean_closure_set(v___f_2272_, 4, v_rlvl_2252_);
lean_closure_set(v___f_2272_, 5, v_fs_2255_);
lean_closure_set(v___f_2272_, 6, v_minor__type_2256_);
lean_closure_set(v___f_2272_, 7, v_tail_2271_);
lean_inc(v_a_2262_);
lean_inc_ref(v_a_2261_);
lean_inc(v_a_2260_);
lean_inc_ref(v_a_2259_);
v___x_2273_ = lean_infer_type(v_head_2270_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___x_2275_ = 0;
v___x_2276_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2274_, v___f_2272_, v___x_2275_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2276_;
}
else
{
lean_dec_ref(v___f_2272_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2277_, lean_object* v_rlvl_2278_, lean_object* v_motives_2279_, lean_object* v_belows_2280_, lean_object* v_fs_2281_, lean_object* v_minor__type_2282_, lean_object* v_tail_2283_, uint8_t v___x_2284_, uint8_t v___x_2285_, uint8_t v___x_2286_, lean_object* v_arg_x27_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_inc_ref(v_arg_x27_2287_);
v___x_2293_ = lean_array_push(v_prods_2277_, v_arg_x27_2287_);
v___x_2294_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2278_, v_motives_2279_, v_belows_2280_, v_fs_2281_, v_minor__type_2282_, v___x_2293_, v_tail_2283_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_mk_empty_array_with_capacity(v___x_2296_);
v___x_2298_ = lean_array_push(v___x_2297_, v_arg_x27_2287_);
v___x_2299_ = l_Lean_Meta_mkLambdaFVars(v___x_2298_, v_a_2295_, v___x_2284_, v___x_2285_, v___x_2284_, v___x_2285_, v___x_2286_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec_ref(v___x_2298_);
return v___x_2299_;
}
else
{
lean_dec_ref(v_arg_x27_2287_);
return v___x_2294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2300_, lean_object* v_rlvl_2301_, lean_object* v_motives_2302_, lean_object* v_belows_2303_, lean_object* v_fs_2304_, lean_object* v_minor__type_2305_, lean_object* v_tail_2306_, lean_object* v___x_2307_, lean_object* v___x_2308_, lean_object* v___x_2309_, lean_object* v_arg_x27_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
uint8_t v___x_1748__boxed_2316_; uint8_t v___x_1749__boxed_2317_; uint8_t v___x_1750__boxed_2318_; lean_object* v_res_2319_; 
v___x_1748__boxed_2316_ = lean_unbox(v___x_2307_);
v___x_1749__boxed_2317_ = lean_unbox(v___x_2308_);
v___x_1750__boxed_2318_ = lean_unbox(v___x_2309_);
v_res_2319_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2300_, v_rlvl_2301_, v_motives_2302_, v_belows_2303_, v_fs_2304_, v_minor__type_2305_, v_tail_2306_, v___x_1748__boxed_2316_, v___x_1749__boxed_2317_, v___x_1750__boxed_2318_, v_arg_x27_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2320_, lean_object* v_head_2321_, lean_object* v_belows_2322_, lean_object* v_arg__type_2323_, lean_object* v_prods_2324_, lean_object* v_rlvl_2325_, lean_object* v_fs_2326_, lean_object* v_minor__type_2327_, lean_object* v_tail_2328_, lean_object* v_arg__args_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
if (lean_obj_tag(v_x_2330_) == 5)
{
lean_object* v_fn_2338_; lean_object* v_arg_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_fn_2338_ = lean_ctor_get(v_x_2330_, 0);
lean_inc_ref(v_fn_2338_);
v_arg_2339_ = lean_ctor_get(v_x_2330_, 1);
lean_inc_ref(v_arg_2339_);
lean_dec_ref_known(v_x_2330_, 2);
v___x_2340_ = lean_array_set(v_x_2331_, v_x_2332_, v_arg_2339_);
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_nat_sub(v_x_2332_, v___x_2341_);
lean_dec(v_x_2332_);
v_x_2330_ = v_fn_2338_;
v_x_2331_ = v___x_2340_;
v_x_2332_ = v___x_2342_;
goto _start;
}
else
{
lean_object* v___x_2344_; 
lean_dec(v_x_2332_);
v___x_2344_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2320_, v_x_2330_);
lean_dec_ref(v_x_2330_);
if (lean_obj_tag(v___x_2344_) == 1)
{
lean_object* v_val_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l_Lean_instInhabitedExpr;
v___x_2347_ = l_Lean_Expr_fvarId_x21(v_head_2321_);
lean_dec_ref(v_head_2321_);
v___x_2348_ = l_Lean_FVarId_getUserName___redArg(v___x_2347_, v___y_2333_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = lean_array_get_borrowed(v___x_2346_, v_belows_2322_, v_val_2345_);
lean_dec(v_val_2345_);
lean_inc(v___x_2350_);
v___x_2351_ = l_Lean_mkAppN(v___x_2350_, v_x_2331_);
lean_dec_ref(v_x_2331_);
v___x_2352_ = l_Lean_Meta_mkPProd(v_arg__type_2323_, v___x_2351_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; uint8_t v___x_2354_; uint8_t v___x_2355_; uint8_t v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___f_2360_; lean_object* v___x_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = 0;
v___x_2355_ = 1;
v___x_2356_ = 1;
v___x_2357_ = lean_box(v___x_2354_);
v___x_2358_ = lean_box(v___x_2355_);
v___x_2359_ = lean_box(v___x_2356_);
v___f_2360_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2360_, 0, v_prods_2324_);
lean_closure_set(v___f_2360_, 1, v_rlvl_2325_);
lean_closure_set(v___f_2360_, 2, v_motives_2320_);
lean_closure_set(v___f_2360_, 3, v_belows_2322_);
lean_closure_set(v___f_2360_, 4, v_fs_2326_);
lean_closure_set(v___f_2360_, 5, v_minor__type_2327_);
lean_closure_set(v___f_2360_, 6, v_tail_2328_);
lean_closure_set(v___f_2360_, 7, v___x_2357_);
lean_closure_set(v___f_2360_, 8, v___x_2358_);
lean_closure_set(v___f_2360_, 9, v___x_2359_);
v___x_2361_ = l_Lean_Meta_mkForallFVars(v_arg__args_2329_, v_a_2353_, v___x_2354_, v___x_2355_, v___x_2355_, v___x_2356_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2349_, v_a_2362_, v___f_2360_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2363_;
}
else
{
lean_dec_ref(v___f_2360_);
lean_dec(v_a_2349_);
return v___x_2361_;
}
}
else
{
lean_dec(v_a_2349_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_minor__type_2327_);
lean_dec_ref(v_fs_2326_);
lean_dec(v_rlvl_2325_);
lean_dec_ref(v_prods_2324_);
lean_dec_ref(v_belows_2322_);
lean_dec_ref(v_motives_2320_);
return v___x_2352_;
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_val_2345_);
lean_dec_ref(v_x_2331_);
lean_dec(v_tail_2328_);
lean_dec_ref(v_minor__type_2327_);
lean_dec_ref(v_fs_2326_);
lean_dec(v_rlvl_2325_);
lean_dec_ref(v_prods_2324_);
lean_dec_ref(v_arg__type_2323_);
lean_dec_ref(v_belows_2322_);
lean_dec_ref(v_motives_2320_);
v_a_2364_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2348_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2348_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v___x_2372_; 
lean_dec(v___x_2344_);
lean_dec_ref(v_x_2331_);
lean_dec_ref(v_arg__type_2323_);
v___x_2372_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2325_, v_motives_2320_, v_belows_2322_, v_fs_2326_, v_minor__type_2327_, v_prods_2324_, v_tail_2328_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; lean_object* v___x_2380_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = lean_unsigned_to_nat(1u);
v___x_2375_ = lean_mk_empty_array_with_capacity(v___x_2374_);
v___x_2376_ = lean_array_push(v___x_2375_, v_head_2321_);
v___x_2377_ = 0;
v___x_2378_ = 1;
v___x_2379_ = 1;
v___x_2380_ = l_Lean_Meta_mkLambdaFVars(v___x_2376_, v_a_2373_, v___x_2377_, v___x_2378_, v___x_2377_, v___x_2378_, v___x_2379_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec_ref(v___x_2376_);
return v___x_2380_;
}
else
{
lean_dec_ref(v_head_2321_);
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2381_, lean_object* v_head_2382_, lean_object* v_belows_2383_, lean_object* v_prods_2384_, lean_object* v_rlvl_2385_, lean_object* v_fs_2386_, lean_object* v_minor__type_2387_, lean_object* v_tail_2388_, lean_object* v_arg__args_2389_, lean_object* v_arg__type_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v_dummy_2396_; lean_object* v_nargs_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_dummy_2396_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2397_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2390_);
lean_inc(v_nargs_2397_);
v___x_2398_ = lean_mk_array(v_nargs_2397_, v_dummy_2396_);
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_sub(v_nargs_2397_, v___x_2399_);
lean_dec(v_nargs_2397_);
lean_inc_ref(v_arg__type_2390_);
v___x_2401_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2381_, v_head_2382_, v_belows_2383_, v_arg__type_2390_, v_prods_2384_, v_rlvl_2385_, v_fs_2386_, v_minor__type_2387_, v_tail_2388_, v_arg__args_2389_, v_arg__type_2390_, v___x_2398_, v___x_2400_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2402_, lean_object* v_motives_2403_, lean_object* v_belows_2404_, lean_object* v_fs_2405_, lean_object* v_minor__type_2406_, lean_object* v_prods_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2402_, v_motives_2403_, v_belows_2404_, v_fs_2405_, v_minor__type_2406_, v_prods_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2415_ = _args[0];
lean_object* v_head_2416_ = _args[1];
lean_object* v_belows_2417_ = _args[2];
lean_object* v_arg__type_2418_ = _args[3];
lean_object* v_prods_2419_ = _args[4];
lean_object* v_rlvl_2420_ = _args[5];
lean_object* v_fs_2421_ = _args[6];
lean_object* v_minor__type_2422_ = _args[7];
lean_object* v_tail_2423_ = _args[8];
lean_object* v_arg__args_2424_ = _args[9];
lean_object* v_x_2425_ = _args[10];
lean_object* v_x_2426_ = _args[11];
lean_object* v_x_2427_ = _args[12];
lean_object* v___y_2428_ = _args[13];
lean_object* v___y_2429_ = _args[14];
lean_object* v___y_2430_ = _args[15];
lean_object* v___y_2431_ = _args[16];
lean_object* v___y_2432_ = _args[17];
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2415_, v_head_2416_, v_belows_2417_, v_arg__type_2418_, v_prods_2419_, v_rlvl_2420_, v_fs_2421_, v_minor__type_2422_, v_tail_2423_, v_arg__args_2424_, v_x_2425_, v_x_2426_, v_x_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec_ref(v_arg__args_2424_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2434_, lean_object* v_motives_2435_, lean_object* v_belows_2436_, lean_object* v_fs_2437_, lean_object* v_minor__args_2438_, lean_object* v_minor__type_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2446_ = lean_array_to_list(v_minor__args_2438_);
v___x_2447_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2434_, v_motives_2435_, v_belows_2436_, v_fs_2437_, v_minor__type_2439_, v___x_2445_, v___x_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2448_, lean_object* v_motives_2449_, lean_object* v_belows_2450_, lean_object* v_fs_2451_, lean_object* v_minor__args_2452_, lean_object* v_minor__type_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2448_, v_motives_2449_, v_belows_2450_, v_fs_2451_, v_minor__args_2452_, v_minor__type_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2460_, lean_object* v_motives_2461_, lean_object* v_belows_2462_, lean_object* v_fs_2463_, lean_object* v_minorType_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___f_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2470_, 0, v_rlvl_2460_);
lean_closure_set(v___f_2470_, 1, v_motives_2461_);
lean_closure_set(v___f_2470_, 2, v_belows_2462_);
lean_closure_set(v___f_2470_, 3, v_fs_2463_);
v___x_2471_ = 0;
v___x_2472_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2464_, v___f_2470_, v___x_2471_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2473_, lean_object* v_motives_2474_, lean_object* v_belows_2475_, lean_object* v_fs_2476_, lean_object* v_minorType_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2473_, v_motives_2474_, v_belows_2475_, v_fs_2476_, v_minorType_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___f_2490_; lean_object* v___x_27155__overap_2491_; lean_object* v___x_2492_; 
v___f_2490_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27155__overap_2491_ = lean_panic_fn_borrowed(v___f_2490_, v_msg_2484_);
lean_inc(v___y_2488_);
lean_inc_ref(v___y_2487_);
lean_inc(v___y_2486_);
lean_inc_ref(v___y_2485_);
v___x_2492_ = lean_apply_5(v___x_27155__overap_2491_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, lean_box(0));
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(lean_object* v_e_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = l_Lean_Expr_hasMVar(v_e_2500_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_e_2500_);
return v___x_2504_;
}
else
{
lean_object* v___x_2505_; lean_object* v_mctx_2506_; lean_object* v___x_2507_; lean_object* v_fst_2508_; lean_object* v_snd_2509_; lean_object* v___x_2510_; lean_object* v_cache_2511_; lean_object* v_zetaDeltaFVarIds_2512_; lean_object* v_postponed_2513_; lean_object* v_diag_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2523_; 
v___x_2505_ = lean_st_ref_get(v___y_2501_);
v_mctx_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc_ref(v_mctx_2506_);
lean_dec(v___x_2505_);
v___x_2507_ = l_Lean_instantiateMVarsCore(v_mctx_2506_, v_e_2500_);
v_fst_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_fst_2508_);
v_snd_2509_ = lean_ctor_get(v___x_2507_, 1);
lean_inc(v_snd_2509_);
lean_dec_ref(v___x_2507_);
v___x_2510_ = lean_st_ref_take(v___y_2501_);
v_cache_2511_ = lean_ctor_get(v___x_2510_, 1);
v_zetaDeltaFVarIds_2512_ = lean_ctor_get(v___x_2510_, 2);
v_postponed_2513_ = lean_ctor_get(v___x_2510_, 3);
v_diag_2514_ = lean_ctor_get(v___x_2510_, 4);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2510_, 0);
lean_dec(v_unused_2524_);
v___x_2516_ = v___x_2510_;
v_isShared_2517_ = v_isSharedCheck_2523_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_diag_2514_);
lean_inc(v_postponed_2513_);
lean_inc(v_zetaDeltaFVarIds_2512_);
lean_inc(v_cache_2511_);
lean_dec(v___x_2510_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2523_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v_snd_2509_);
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_snd_2509_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_cache_2511_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_zetaDeltaFVarIds_2512_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_postponed_2513_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_diag_2514_);
v___x_2519_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_st_ref_put(v___y_2501_, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_fst_2508_);
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg___boxed(lean_object* v_e_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2525_, v___y_2526_);
lean_dec(v___y_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_e_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_e_2529_, v___y_2531_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_e_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_e_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_thm_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v_env_2547_; lean_object* v_toConstantVal_2548_; lean_object* v_value_2549_; lean_object* v_all_2550_; uint8_t v___y_2552_; lean_object* v_type_2560_; uint8_t v___x_2561_; 
v___x_2546_ = lean_st_ref_get(v___y_2544_);
v_env_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc_ref_n(v_env_2547_, 2);
lean_dec(v___x_2546_);
v_toConstantVal_2548_ = lean_ctor_get(v_thm_2543_, 0);
v_value_2549_ = lean_ctor_get(v_thm_2543_, 1);
v_all_2550_ = lean_ctor_get(v_thm_2543_, 2);
v_type_2560_ = lean_ctor_get(v_toConstantVal_2548_, 2);
v___x_2561_ = l_Lean_Environment_hasUnsafe(v_env_2547_, v_type_2560_);
if (v___x_2561_ == 0)
{
uint8_t v___x_2562_; 
v___x_2562_ = l_Lean_Environment_hasUnsafe(v_env_2547_, v_value_2549_);
v___y_2552_ = v___x_2562_;
goto v___jp_2551_;
}
else
{
lean_dec_ref(v_env_2547_);
v___y_2552_ = v___x_2561_;
goto v___jp_2551_;
}
v___jp_2551_:
{
if (v___y_2552_ == 0)
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_thm_2543_);
v___x_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
else
{
lean_object* v___x_2555_; uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_inc(v_all_2550_);
lean_inc_ref(v_value_2549_);
lean_inc_ref(v_toConstantVal_2548_);
lean_dec_ref(v_thm_2543_);
v___x_2555_ = lean_box(0);
v___x_2556_ = 0;
v___x_2557_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2557_, 0, v_toConstantVal_2548_);
lean_ctor_set(v___x_2557_, 1, v_value_2549_);
lean_ctor_set(v___x_2557_, 2, v___x_2555_);
lean_ctor_set(v___x_2557_, 3, v_all_2550_);
lean_ctor_set_uint8(v___x_2557_, sizeof(void*)*4, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
return v___x_2559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_thm_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2563_, v___y_2564_);
lean_dec(v___y_2564_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_thm_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_thm_2567_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_thm_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_thm_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2582_, lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v_all_2585_, lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v_x_2589_){
_start:
{
lean_object* v___y_2591_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = lean_array_get_size(v_all_2585_);
v___x_2596_ = lean_nat_dec_lt(v_x_2589_, v___x_2595_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2597_ = lean_array_get_borrowed(v___x_2586_, v_all_2585_, v___x_2587_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2599_ = lean_nat_sub(v_x_2589_, v___x_2595_);
v___x_2600_ = lean_nat_add(v___x_2599_, v___x_2588_);
lean_dec(v___x_2599_);
v___x_2601_ = l_Nat_reprFast(v___x_2600_);
v___x_2602_ = lean_string_append(v___x_2598_, v___x_2601_);
lean_dec_ref(v___x_2601_);
lean_inc(v___x_2597_);
v___x_2603_ = l_Lean_Name_str___override(v___x_2597_, v___x_2602_);
v___y_2591_ = v___x_2603_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_array_fget_borrowed(v_all_2585_, v_x_2589_);
lean_inc(v___x_2604_);
v___x_2605_ = l_Lean_mkBelowName(v___x_2604_);
v___y_2591_ = v___x_2605_;
goto v___jp_2590_;
}
v___jp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = l_Lean_Expr_const___override(v___y_2591_, v___x_2582_);
v___x_2593_ = l_Array_append___redArg(v___x_2583_, v___x_2584_);
v___x_2594_ = l_Lean_mkAppN(v___x_2592_, v___x_2593_);
lean_dec_ref(v___x_2593_);
return v___x_2594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2606_, lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v_all_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v_x_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2606_, v___x_2607_, v___x_2608_, v_all_2609_, v___x_2610_, v___x_2611_, v___x_2612_, v_x_2613_);
lean_dec(v_x_2613_);
lean_dec(v___x_2612_);
lean_dec(v___x_2611_);
lean_dec(v___x_2610_);
lean_dec_ref(v_all_2609_);
lean_dec_ref(v___x_2608_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v___x_2617_, lean_object* v_fs_2618_, lean_object* v_as_2619_, size_t v_sz_2620_, size_t v_i_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_lt(v_i_2621_, v_sz_2620_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_dec_ref(v_fs_2618_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v___x_2616_);
lean_dec(v___x_2615_);
v___x_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2629_, 0, v_b_2622_);
return v___x_2629_;
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2631_; 
v_a_2630_ = lean_array_uget_borrowed(v_as_2619_, v_i_2621_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc_ref(v___y_2623_);
lean_inc(v_a_2630_);
v___x_2631_ = lean_infer_type(v_a_2630_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
lean_inc_ref(v_fs_2618_);
lean_inc_ref(v___x_2617_);
lean_inc_ref(v___x_2616_);
lean_inc(v___x_2615_);
v___x_2633_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2615_, v___x_2616_, v___x_2617_, v_fs_2618_, v_a_2632_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; size_t v___x_2636_; size_t v___x_2637_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
v___x_2635_ = l_Lean_Expr_app___override(v_b_2622_, v_a_2634_);
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_add(v_i_2621_, v___x_2636_);
v_i_2621_ = v___x_2637_;
v_b_2622_ = v___x_2635_;
goto _start;
}
else
{
lean_dec_ref(v_b_2622_);
lean_dec_ref(v_fs_2618_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v___x_2616_);
lean_dec(v___x_2615_);
return v___x_2633_;
}
}
else
{
lean_dec_ref(v_b_2622_);
lean_dec_ref(v_fs_2618_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v___x_2616_);
lean_dec(v___x_2615_);
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v_fs_2642_, lean_object* v_as_2643_, lean_object* v_sz_2644_, lean_object* v_i_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
size_t v_sz_boxed_2652_; size_t v_i_boxed_2653_; lean_object* v_res_2654_; 
v_sz_boxed_2652_ = lean_unbox_usize(v_sz_2644_);
lean_dec(v_sz_2644_);
v_i_boxed_2653_ = lean_unbox_usize(v_i_2645_);
lean_dec(v_i_2645_);
v_res_2654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2639_, v___x_2640_, v___x_2641_, v_fs_2642_, v_as_2643_, v_sz_boxed_2652_, v_i_boxed_2653_, v_b_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec_ref(v_as_2643_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_a_2655_, lean_object* v___x_2656_, uint8_t v___x_2657_, lean_object* v_targs_2658_, lean_object* v_x_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = l_Lean_mkAppN(v_a_2655_, v_targs_2658_);
v___x_2666_ = l_Lean_mkAppN(v___x_2656_, v_targs_2658_);
v___x_2667_ = l_Lean_Meta_mkPProd(v___x_2665_, v___x_2666_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; uint8_t v___x_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v___x_2669_ = 0;
v___x_2670_ = 1;
v___x_2671_ = l_Lean_Meta_mkLambdaFVars(v_targs_2658_, v_a_2668_, v___x_2669_, v___x_2657_, v___x_2669_, v___x_2657_, v___x_2670_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
return v___x_2671_;
}
else
{
return v___x_2667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_a_2672_, lean_object* v___x_2673_, lean_object* v___x_2674_, lean_object* v_targs_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v___x_30426__boxed_2682_; lean_object* v_res_2683_; 
v___x_30426__boxed_2682_ = lean_unbox(v___x_2674_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_a_2672_, v___x_2673_, v___x_30426__boxed_2682_, v_targs_2675_, v_x_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec_ref(v_x_2676_);
lean_dec_ref(v_targs_2675_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v_as_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_usize_dec_lt(v_i_2688_, v_sz_2687_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_b_2689_);
return v___x_2696_;
}
else
{
lean_object* v_snd_2697_; lean_object* v_fst_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2755_; 
v_snd_2697_ = lean_ctor_get(v_b_2689_, 1);
v_fst_2698_ = lean_ctor_get(v_b_2689_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_b_2689_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2700_ = v_b_2689_;
v_isShared_2701_ = v_isSharedCheck_2755_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_snd_2697_);
lean_inc(v_fst_2698_);
lean_dec(v_b_2689_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2755_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_array_2702_; lean_object* v_start_2703_; lean_object* v_stop_2704_; uint8_t v___x_2705_; 
v_array_2702_ = lean_ctor_get(v_snd_2697_, 0);
v_start_2703_ = lean_ctor_get(v_snd_2697_, 1);
v_stop_2704_ = lean_ctor_get(v_snd_2697_, 2);
v___x_2705_ = lean_nat_dec_lt(v_start_2703_, v_stop_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2707_; 
if (v_isShared_2701_ == 0)
{
v___x_2707_ = v___x_2700_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_fst_2698_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_snd_2697_);
v___x_2707_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
else
{
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2751_; 
lean_inc(v_stop_2704_);
lean_inc(v_start_2703_);
lean_inc_ref(v_array_2702_);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_snd_2697_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; lean_object* v_unused_2753_; lean_object* v_unused_2754_; 
v_unused_2752_ = lean_ctor_get(v_snd_2697_, 2);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_snd_2697_, 1);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_snd_2697_, 0);
lean_dec(v_unused_2754_);
v___x_2711_ = v_snd_2697_;
v_isShared_2712_ = v_isSharedCheck_2751_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v_snd_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2751_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
uint8_t v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2713_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
v_a_2714_ = lean_array_uget_borrowed(v_as_2686_, v_i_2688_);
v___x_2715_ = lean_array_fget_borrowed(v_array_2702_, v_start_2703_);
v___x_2716_ = lean_box(v___x_2713_);
lean_inc(v___x_2715_);
lean_inc(v_a_2714_);
v___f_2717_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2717_, 0, v_a_2714_);
lean_closure_set(v___f_2717_, 1, v___x_2715_);
lean_closure_set(v___f_2717_, 2, v___x_2716_);
v___x_2718_ = lean_unsigned_to_nat(1u);
v___x_2719_ = lean_nat_add(v_start_2703_, v___x_2718_);
lean_dec(v_start_2703_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2719_);
v___x_2721_ = v___x_2711_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_array_2702_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_stop_2704_);
v___x_2721_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; 
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v_a_2714_);
v___x_2722_ = lean_infer_type(v_a_2714_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; uint8_t v___x_2724_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = 0;
v___x_2725_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2723_, v___f_2717_, v___x_2724_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = l_Lean_Expr_app___override(v_fst_2698_, v_a_2726_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2721_);
lean_ctor_set(v___x_2700_, 0, v___x_2727_);
v___x_2729_ = v___x_2700_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2721_);
v___x_2729_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
size_t v___x_2730_; size_t v___x_2731_; 
v___x_2730_ = ((size_t)1ULL);
v___x_2731_ = lean_usize_add(v_i_2688_, v___x_2730_);
v_i_2688_ = v___x_2731_;
v_b_2689_ = v___x_2729_;
goto _start;
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v___x_2721_);
lean_del_object(v___x_2700_);
lean_dec(v_fst_2698_);
v_a_2734_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2725_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2725_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec_ref(v___x_2721_);
lean_dec_ref(v___f_2717_);
lean_del_object(v___x_2700_);
lean_dec(v_fst_2698_);
v_a_2742_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2722_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2722_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_2756_, lean_object* v___x_2757_, lean_object* v_as_2758_, lean_object* v_sz_2759_, lean_object* v_i_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
size_t v_sz_boxed_2767_; size_t v_i_boxed_2768_; lean_object* v_res_2769_; 
v_sz_boxed_2767_ = lean_unbox_usize(v_sz_2759_);
lean_dec(v_sz_2759_);
v_i_boxed_2768_ = lean_unbox_usize(v_i_2760_);
lean_dec(v_i_2760_);
v_res_2769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2756_, v___x_2757_, v_as_2758_, v_sz_boxed_2767_, v_i_boxed_2768_, v_b_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_as_2758_);
lean_dec(v___x_2757_);
lean_dec(v___x_2756_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v_as_2770_, size_t v_sz_2771_, size_t v_i_2772_, lean_object* v_b_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = lean_usize_dec_lt(v_i_2772_, v_sz_2771_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_b_2773_);
return v___x_2780_;
}
else
{
lean_object* v_a_2781_; lean_object* v_toInductionSubgoal_2782_; lean_object* v_mvarId_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_a_2781_ = lean_array_uget_borrowed(v_as_2770_, v_i_2772_);
v_toInductionSubgoal_2782_ = lean_ctor_get(v_a_2781_, 0);
v_mvarId_2783_ = lean_ctor_get(v_toInductionSubgoal_2782_, 0);
v___x_2784_ = 0;
v___x_2785_ = lean_box(0);
lean_inc(v_mvarId_2783_);
v___x_2786_ = l_Lean_MVarId_refl(v_mvarId_2783_, v___x_2784_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2786_) == 0)
{
size_t v___x_2787_; size_t v___x_2788_; 
lean_dec_ref_known(v___x_2786_, 1);
v___x_2787_ = ((size_t)1ULL);
v___x_2788_ = lean_usize_add(v_i_2772_, v___x_2787_);
v_i_2772_ = v___x_2788_;
v_b_2773_ = v___x_2785_;
goto _start;
}
else
{
return v___x_2786_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v_as_2790_, lean_object* v_sz_2791_, lean_object* v_i_2792_, lean_object* v_b_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_sz_boxed_2799_; size_t v_i_boxed_2800_; lean_object* v_res_2801_; 
v_sz_boxed_2799_ = lean_unbox_usize(v_sz_2791_);
lean_dec(v_sz_2791_);
v_i_boxed_2800_ = lean_unbox_usize(v_i_2792_);
lean_dec(v_i_2792_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_as_2790_, v_sz_boxed_2799_, v_i_boxed_2800_, v_b_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v_as_2790_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2802_, lean_object* v_tail_2803_, lean_object* v_recName_2804_, lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_val_2816_, uint8_t v___x_2817_, lean_object* v_brecOnGoName_2818_, lean_object* v_levelParams_2819_, lean_object* v___x_2820_, lean_object* v_brecOnName_2821_, lean_object* v___x_2822_, lean_object* v_brecOnEqName_2823_, lean_object* v_fs_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; size_t v_sz_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
lean_inc(v___x_2802_);
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2802_);
lean_ctor_set(v___x_2830_, 1, v_tail_2803_);
v___x_2831_ = l_Lean_Expr_const___override(v_recName_2804_, v___x_2830_);
v___x_2832_ = l_Lean_mkAppN(v___x_2831_, v___x_2805_);
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v___x_2806_);
v_sz_2834_ = lean_array_size(v___x_2807_);
v___x_2835_ = ((size_t)0ULL);
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_2808_, v___x_2809_, v___x_2807_, v_sz_2834_, v___x_2835_, v___x_2833_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v_fst_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_3199_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v_fst_2838_ = lean_ctor_get(v_a_2837_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_a_2837_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v_a_2837_, 1);
lean_dec(v_unused_3200_);
v___x_2840_ = v_a_2837_;
v_isShared_2841_ = v_isSharedCheck_3199_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_fst_2838_);
lean_dec(v_a_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_3199_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
size_t v_sz_2842_; lean_object* v___x_2843_; 
v_sz_2842_ = lean_array_size(v___x_2810_);
lean_inc_ref(v_fs_2824_);
lean_inc_ref(v___x_2811_);
lean_inc_ref(v___x_2807_);
v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2802_, v___x_2807_, v___x_2811_, v_fs_2824_, v___x_2810_, v_sz_2842_, v___x_2835_, v_fst_2838_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
v___x_2845_ = l_Lean_mkAppN(v_a_2844_, v___x_2812_);
lean_inc_ref_n(v___x_2813_, 3);
v___x_2846_ = l_Lean_Expr_app___override(v___x_2845_, v___x_2813_);
v___x_2847_ = l_Array_append___redArg(v___x_2805_, v___x_2807_);
v___x_2848_ = l_Array_append___redArg(v___x_2847_, v___x_2812_);
v___x_2849_ = lean_mk_empty_array_with_capacity(v___x_2814_);
v___x_2850_ = lean_array_push(v___x_2849_, v___x_2813_);
v___x_2851_ = l_Array_append___redArg(v___x_2848_, v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Array_append___redArg(v___x_2851_, v_fs_2824_);
v___x_2853_ = lean_array_get(v___x_2815_, v___x_2807_, v_val_2816_);
lean_dec_ref(v___x_2807_);
v___x_2854_ = lean_array_push(v___x_2812_, v___x_2813_);
v___x_2855_ = l_Lean_mkAppN(v___x_2853_, v___x_2854_);
v___x_2856_ = lean_array_get(v___x_2815_, v___x_2811_, v_val_2816_);
lean_dec_ref(v___x_2811_);
v___x_2857_ = l_Lean_mkAppN(v___x_2856_, v___x_2854_);
lean_inc_ref(v___x_2855_);
v___x_2858_ = l_Lean_Meta_mkPProd(v___x_2855_, v___x_2857_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; uint8_t v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = 0;
v___x_2861_ = 1;
v___x_2862_ = l_Lean_Meta_mkForallFVars(v___x_2852_, v_a_2859_, v___x_2860_, v___x_2817_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = l_Lean_Meta_mkLambdaFVars(v___x_2852_, v___x_2846_, v___x_2860_, v___x_2817_, v___x_2860_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_3166_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = lean_box(1);
lean_inc(v_levelParams_2819_);
lean_inc(v_brecOnGoName_2818_);
v___x_2867_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2818_, v_levelParams_2819_, v_a_2863_, v_a_2865_, v___x_2866_, v___y_2828_);
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_3166_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_3166_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
lean_inc(v_a_2868_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 1);
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_3165_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_addDecl(v___x_2873_, v___x_2860_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_toConstantVal_2875_; lean_object* v_name_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref_known(v___x_2874_, 1);
v_toConstantVal_2875_ = lean_ctor_get(v_a_2868_, 0);
lean_inc_ref(v_toConstantVal_2875_);
lean_dec(v_a_2868_);
v_name_2876_ = lean_ctor_get(v_toConstantVal_2875_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_toConstantVal_2875_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; 
v_unused_3163_ = lean_ctor_get(v_toConstantVal_2875_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_toConstantVal_2875_, 1);
lean_dec(v_unused_3164_);
v___x_2878_ = v_toConstantVal_2875_;
v_isShared_2879_ = v_isSharedCheck_3162_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_name_2876_);
lean_dec(v_toConstantVal_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_3162_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_env_2882_; lean_object* v_nextMacroScope_2883_; lean_object* v_ngen_2884_; lean_object* v_auxDeclNGen_2885_; lean_object* v_traceState_2886_; lean_object* v_messages_2887_; lean_object* v_infoState_2888_; lean_object* v_snapshotTasks_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_name_2876_);
v___x_2880_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2876_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref(v___x_2880_);
v___x_2881_ = lean_st_ref_take(v___y_2828_);
v_env_2882_ = lean_ctor_get(v___x_2881_, 0);
v_nextMacroScope_2883_ = lean_ctor_get(v___x_2881_, 1);
v_ngen_2884_ = lean_ctor_get(v___x_2881_, 2);
v_auxDeclNGen_2885_ = lean_ctor_get(v___x_2881_, 3);
v_traceState_2886_ = lean_ctor_get(v___x_2881_, 4);
v_messages_2887_ = lean_ctor_get(v___x_2881_, 6);
v_infoState_2888_ = lean_ctor_get(v___x_2881_, 7);
v_snapshotTasks_2889_ = lean_ctor_get(v___x_2881_, 8);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v___x_2881_, 5);
lean_dec(v_unused_3161_);
v___x_2891_ = v___x_2881_;
v_isShared_2892_ = v_isSharedCheck_3160_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_snapshotTasks_2889_);
lean_inc(v_infoState_2888_);
lean_inc(v_messages_2887_);
lean_inc(v_traceState_2886_);
lean_inc(v_auxDeclNGen_2885_);
lean_inc(v_ngen_2884_);
lean_inc(v_nextMacroScope_2883_);
lean_inc(v_env_2882_);
lean_dec(v___x_2881_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_3160_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2893_ = l_Lean_addProtected(v_env_2882_, v_name_2876_);
v___x_2894_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 5, v___x_2894_);
lean_ctor_set(v___x_2891_, 0, v___x_2893_);
v___x_2896_ = v___x_2891_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_nextMacroScope_2883_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_ngen_2884_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_auxDeclNGen_2885_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_traceState_2886_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_messages_2887_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_infoState_2888_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_snapshotTasks_2889_);
v___x_2896_ = v_reuseFailAlloc_3159_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_mctx_2899_; lean_object* v_zetaDeltaFVarIds_2900_; lean_object* v_postponed_2901_; lean_object* v_diag_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_3157_; 
v___x_2897_ = lean_st_ref_put(v___y_2828_, v___x_2896_);
v___x_2898_ = lean_st_ref_take(v___y_2826_);
v_mctx_2899_ = lean_ctor_get(v___x_2898_, 0);
v_zetaDeltaFVarIds_2900_ = lean_ctor_get(v___x_2898_, 2);
v_postponed_2901_ = lean_ctor_get(v___x_2898_, 3);
v_diag_2902_ = lean_ctor_get(v___x_2898_, 4);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_2898_, 1);
lean_dec(v_unused_3158_);
v___x_2904_ = v___x_2898_;
v_isShared_2905_ = v_isSharedCheck_3157_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_diag_2902_);
lean_inc(v_postponed_2901_);
lean_inc(v_zetaDeltaFVarIds_2900_);
lean_inc(v_mctx_2899_);
lean_dec(v___x_2898_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_3157_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 1, v___x_2906_);
v___x_2908_ = v___x_2904_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_mctx_2899_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_zetaDeltaFVarIds_2900_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_postponed_2901_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_diag_2902_);
v___x_2908_ = v_reuseFailAlloc_3156_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2909_ = lean_st_ref_put(v___y_2826_, v___x_2908_);
lean_inc(v___x_2820_);
v___x_2910_ = l_Lean_Expr_const___override(v_brecOnGoName_2818_, v___x_2820_);
v___x_2911_ = l_Lean_mkAppN(v___x_2910_, v___x_2852_);
lean_inc_ref(v___x_2911_);
v___x_2912_ = l_Lean_Meta_mkPProdFstM(v___x_2911_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = l_Lean_Meta_mkLambdaFVars(v___x_2852_, v_a_2913_, v___x_2860_, v___x_2817_, v___x_2860_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = l_Lean_Meta_mkForallFVars(v___x_2852_, v___x_2855_, v___x_2860_, v___x_2817_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_3131_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
lean_inc(v_levelParams_2819_);
v___x_2918_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2821_, v_levelParams_2819_, v_a_2917_, v_a_2915_, v___x_2866_, v___y_2828_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_3131_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_3131_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
lean_inc(v_a_2919_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set_tag(v___x_2921_, 1);
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_3130_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_addDecl(v___x_2924_, v___x_2860_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_toConstantVal_2926_; lean_object* v_name_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref_known(v___x_2925_, 1);
v_toConstantVal_2926_ = lean_ctor_get(v_a_2919_, 0);
lean_inc_ref(v_toConstantVal_2926_);
lean_dec(v_a_2919_);
v_name_2927_ = lean_ctor_get(v_toConstantVal_2926_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_toConstantVal_2926_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; lean_object* v_unused_3129_; 
v_unused_3128_ = lean_ctor_get(v_toConstantVal_2926_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_toConstantVal_2926_, 1);
lean_dec(v_unused_3129_);
v___x_2929_ = v_toConstantVal_2926_;
v_isShared_2930_ = v_isSharedCheck_3127_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_name_2927_);
lean_dec(v_toConstantVal_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_3127_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_env_2933_; lean_object* v_nextMacroScope_2934_; lean_object* v_ngen_2935_; lean_object* v_auxDeclNGen_2936_; lean_object* v_traceState_2937_; lean_object* v_messages_2938_; lean_object* v_infoState_2939_; lean_object* v_snapshotTasks_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_name_2927_);
v___x_2931_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2927_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref(v___x_2931_);
v___x_2932_ = lean_st_ref_take(v___y_2828_);
v_env_2933_ = lean_ctor_get(v___x_2932_, 0);
v_nextMacroScope_2934_ = lean_ctor_get(v___x_2932_, 1);
v_ngen_2935_ = lean_ctor_get(v___x_2932_, 2);
v_auxDeclNGen_2936_ = lean_ctor_get(v___x_2932_, 3);
v_traceState_2937_ = lean_ctor_get(v___x_2932_, 4);
v_messages_2938_ = lean_ctor_get(v___x_2932_, 6);
v_infoState_2939_ = lean_ctor_get(v___x_2932_, 7);
v_snapshotTasks_2940_ = lean_ctor_get(v___x_2932_, 8);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_2932_, 5);
lean_dec(v_unused_3126_);
v___x_2942_ = v___x_2932_;
v_isShared_2943_ = v_isSharedCheck_3125_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snapshotTasks_2940_);
lean_inc(v_infoState_2939_);
lean_inc(v_messages_2938_);
lean_inc(v_traceState_2937_);
lean_inc(v_auxDeclNGen_2936_);
lean_inc(v_ngen_2935_);
lean_inc(v_nextMacroScope_2934_);
lean_inc(v_env_2933_);
lean_dec(v___x_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3125_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2946_; 
lean_inc(v_name_2927_);
v___x_2944_ = l_Lean_markAuxRecursor(v_env_2933_, v_name_2927_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 5, v___x_2894_);
lean_ctor_set(v___x_2942_, 0, v___x_2944_);
v___x_2946_ = v___x_2942_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_nextMacroScope_2934_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_ngen_2935_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_auxDeclNGen_2936_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_traceState_2937_);
lean_ctor_set(v_reuseFailAlloc_3124_, 5, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3124_, 6, v_messages_2938_);
lean_ctor_set(v_reuseFailAlloc_3124_, 7, v_infoState_2939_);
lean_ctor_set(v_reuseFailAlloc_3124_, 8, v_snapshotTasks_2940_);
v___x_2946_ = v_reuseFailAlloc_3124_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_mctx_2949_; lean_object* v_zetaDeltaFVarIds_2950_; lean_object* v_postponed_2951_; lean_object* v_diag_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3122_; 
v___x_2947_ = lean_st_ref_put(v___y_2828_, v___x_2946_);
v___x_2948_ = lean_st_ref_take(v___y_2826_);
v_mctx_2949_ = lean_ctor_get(v___x_2948_, 0);
v_zetaDeltaFVarIds_2950_ = lean_ctor_get(v___x_2948_, 2);
v_postponed_2951_ = lean_ctor_get(v___x_2948_, 3);
v_diag_2952_ = lean_ctor_get(v___x_2948_, 4);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v___x_2948_, 1);
lean_dec(v_unused_3123_);
v___x_2954_ = v___x_2948_;
v_isShared_2955_ = v_isSharedCheck_3122_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_diag_2952_);
lean_inc(v_postponed_2951_);
lean_inc(v_zetaDeltaFVarIds_2950_);
lean_inc(v_mctx_2949_);
lean_dec(v___x_2948_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3122_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2906_);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_mctx_2949_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_zetaDeltaFVarIds_2950_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_postponed_2951_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_diag_2952_);
v___x_2957_ = v_reuseFailAlloc_3121_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_env_2960_; lean_object* v_nextMacroScope_2961_; lean_object* v_ngen_2962_; lean_object* v_auxDeclNGen_2963_; lean_object* v_traceState_2964_; lean_object* v_messages_2965_; lean_object* v_infoState_2966_; lean_object* v_snapshotTasks_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3119_; 
v___x_2958_ = lean_st_ref_put(v___y_2826_, v___x_2957_);
v___x_2959_ = lean_st_ref_take(v___y_2828_);
v_env_2960_ = lean_ctor_get(v___x_2959_, 0);
v_nextMacroScope_2961_ = lean_ctor_get(v___x_2959_, 1);
v_ngen_2962_ = lean_ctor_get(v___x_2959_, 2);
v_auxDeclNGen_2963_ = lean_ctor_get(v___x_2959_, 3);
v_traceState_2964_ = lean_ctor_get(v___x_2959_, 4);
v_messages_2965_ = lean_ctor_get(v___x_2959_, 6);
v_infoState_2966_ = lean_ctor_get(v___x_2959_, 7);
v_snapshotTasks_2967_ = lean_ctor_get(v___x_2959_, 8);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_2959_, 5);
lean_dec(v_unused_3120_);
v___x_2969_ = v___x_2959_;
v_isShared_2970_ = v_isSharedCheck_3119_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_snapshotTasks_2967_);
lean_inc(v_infoState_2966_);
lean_inc(v_messages_2965_);
lean_inc(v_traceState_2964_);
lean_inc(v_auxDeclNGen_2963_);
lean_inc(v_ngen_2962_);
lean_inc(v_nextMacroScope_2961_);
lean_inc(v_env_2960_);
lean_dec(v___x_2959_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3119_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_inc(v_name_2927_);
v___x_2971_ = l_Lean_addProtected(v_env_2960_, v_name_2927_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 5, v___x_2894_);
lean_ctor_set(v___x_2969_, 0, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_nextMacroScope_2961_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v_ngen_2962_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v_auxDeclNGen_2963_);
lean_ctor_set(v_reuseFailAlloc_3118_, 4, v_traceState_2964_);
lean_ctor_set(v_reuseFailAlloc_3118_, 5, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3118_, 6, v_messages_2965_);
lean_ctor_set(v_reuseFailAlloc_3118_, 7, v_infoState_2966_);
lean_ctor_set(v_reuseFailAlloc_3118_, 8, v_snapshotTasks_2967_);
v___x_2973_ = v_reuseFailAlloc_3118_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_mctx_2976_; lean_object* v_zetaDeltaFVarIds_2977_; lean_object* v_postponed_2978_; lean_object* v_diag_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3116_; 
v___x_2974_ = lean_st_ref_put(v___y_2828_, v___x_2973_);
v___x_2975_ = lean_st_ref_take(v___y_2826_);
v_mctx_2976_ = lean_ctor_get(v___x_2975_, 0);
v_zetaDeltaFVarIds_2977_ = lean_ctor_get(v___x_2975_, 2);
v_postponed_2978_ = lean_ctor_get(v___x_2975_, 3);
v_diag_2979_ = lean_ctor_get(v___x_2975_, 4);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_2975_, 1);
lean_dec(v_unused_3117_);
v___x_2981_ = v___x_2975_;
v_isShared_2982_ = v_isSharedCheck_3116_;
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
v_isShared_2982_ = v_isSharedCheck_3116_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_2906_);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_mctx_2976_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_zetaDeltaFVarIds_2977_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_postponed_2978_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_diag_2979_);
v___x_2984_ = v_reuseFailAlloc_3115_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2985_ = lean_st_ref_put(v___y_2826_, v___x_2984_);
v___x_2986_ = l_Lean_Expr_const___override(v_name_2927_, v___x_2820_);
v___x_2987_ = l_Lean_mkAppN(v___x_2986_, v___x_2852_);
v___x_2988_ = lean_array_get(v___x_2815_, v_fs_2824_, v_val_2816_);
lean_dec_ref(v_fs_2824_);
v___x_2989_ = l_Lean_mkAppN(v___x_2988_, v___x_2854_);
lean_dec_ref(v___x_2854_);
v___x_2990_ = l_Lean_Meta_mkPProdSndM(v___x_2911_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = l_Lean_Expr_app___override(v___x_2989_, v_a_2991_);
v___x_2993_ = l_Lean_Meta_mkEq(v___x_2987_, v___x_2992_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc_n(v_a_2994_, 2);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = lean_box(0);
v___x_2996_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2994_, v___x_2995_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = l_Lean_Expr_mvarId_x21(v_a_2997_);
v___x_2999_ = l_Lean_Expr_fvarId_x21(v___x_2813_);
lean_dec_ref(v___x_2813_);
v___x_3000_ = lean_mk_empty_array_with_capacity(v___x_2822_);
v___x_3001_ = lean_box(0);
v___x_3002_ = l_Lean_MVarId_cases(v___x_2998_, v___x_2999_, v___x_3000_, v___x_2860_, v___x_3001_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; size_t v_sz_3005_; lean_object* v___x_3006_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = lean_box(0);
v_sz_3005_ = lean_array_size(v_a_3003_);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v_a_3003_, v_sz_3005_, v___x_2835_, v___x_3004_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v_a_3003_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v___x_3009_; 
lean_dec_ref_known(v___x_3006_, 1);
v___x_3007_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___redArg(v_a_2997_, v___y_2826_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = l_Lean_Meta_mkForallFVars(v___x_2852_, v_a_2994_, v___x_2860_, v___x_2817_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = l_Lean_Meta_mkLambdaFVars(v___x_2852_, v_a_3008_, v___x_2860_, v___x_2817_, v___x_2860_, v___x_2817_, v___x_2861_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec_ref(v___x_2852_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
lean_inc(v_brecOnEqName_2823_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 2, v_a_3010_);
lean_ctor_set(v___x_2929_, 1, v_levelParams_2819_);
lean_ctor_set(v___x_2929_, 0, v_brecOnEqName_2823_);
v___x_3014_ = v___x_2929_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_brecOnEqName_2823_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_levelParams_2819_);
lean_ctor_set(v_reuseFailAlloc_3066_, 2, v_a_3010_);
v___x_3014_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3015_ = lean_box(0);
lean_inc(v_brecOnEqName_2823_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 1);
lean_ctor_set(v___x_2840_, 1, v___x_3015_);
lean_ctor_set(v___x_2840_, 0, v_brecOnEqName_2823_);
v___x_3017_ = v___x_2840_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_brecOnEqName_2823_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3015_);
v___x_3017_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 2, v___x_3017_);
lean_ctor_set(v___x_2878_, 1, v_a_3012_);
lean_ctor_set(v___x_2878_, 0, v___x_3014_);
v___x_3019_ = v___x_2878_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_a_3012_);
lean_ctor_set(v_reuseFailAlloc_3064_, 2, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v_a_3021_; lean_object* v___x_3022_; 
v___x_3020_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v___x_3019_, v___y_2828_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = l_Lean_addDecl(v_a_3021_, v___x_2860_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_3022_, 0);
lean_dec(v_unused_3063_);
v___x_3024_ = v___x_3022_;
v_isShared_3025_ = v_isSharedCheck_3062_;
goto v_resetjp_3023_;
}
else
{
lean_dec(v___x_3022_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3062_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3026_; lean_object* v_env_3027_; lean_object* v_nextMacroScope_3028_; lean_object* v_ngen_3029_; lean_object* v_auxDeclNGen_3030_; lean_object* v_traceState_3031_; lean_object* v_messages_3032_; lean_object* v_infoState_3033_; lean_object* v_snapshotTasks_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3060_; 
v___x_3026_ = lean_st_ref_take(v___y_2828_);
v_env_3027_ = lean_ctor_get(v___x_3026_, 0);
v_nextMacroScope_3028_ = lean_ctor_get(v___x_3026_, 1);
v_ngen_3029_ = lean_ctor_get(v___x_3026_, 2);
v_auxDeclNGen_3030_ = lean_ctor_get(v___x_3026_, 3);
v_traceState_3031_ = lean_ctor_get(v___x_3026_, 4);
v_messages_3032_ = lean_ctor_get(v___x_3026_, 6);
v_infoState_3033_ = lean_ctor_get(v___x_3026_, 7);
v_snapshotTasks_3034_ = lean_ctor_get(v___x_3026_, 8);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_3026_, 5);
lean_dec(v_unused_3061_);
v___x_3036_ = v___x_3026_;
v_isShared_3037_ = v_isSharedCheck_3060_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_snapshotTasks_3034_);
lean_inc(v_infoState_3033_);
lean_inc(v_messages_3032_);
lean_inc(v_traceState_3031_);
lean_inc(v_auxDeclNGen_3030_);
lean_inc(v_ngen_3029_);
lean_inc(v_nextMacroScope_3028_);
lean_inc(v_env_3027_);
lean_dec(v___x_3026_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3060_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3038_ = l_Lean_addProtected(v_env_3027_, v_brecOnEqName_2823_);
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 5, v___x_2894_);
lean_ctor_set(v___x_3036_, 0, v___x_3038_);
v___x_3040_ = v___x_3036_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_nextMacroScope_3028_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v_ngen_3029_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_auxDeclNGen_3030_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v_traceState_3031_);
lean_ctor_set(v_reuseFailAlloc_3059_, 5, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3059_, 6, v_messages_3032_);
lean_ctor_set(v_reuseFailAlloc_3059_, 7, v_infoState_3033_);
lean_ctor_set(v_reuseFailAlloc_3059_, 8, v_snapshotTasks_3034_);
v___x_3040_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v_mctx_3043_; lean_object* v_zetaDeltaFVarIds_3044_; lean_object* v_postponed_3045_; lean_object* v_diag_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3057_; 
v___x_3041_ = lean_st_ref_put(v___y_2828_, v___x_3040_);
v___x_3042_ = lean_st_ref_take(v___y_2826_);
v_mctx_3043_ = lean_ctor_get(v___x_3042_, 0);
v_zetaDeltaFVarIds_3044_ = lean_ctor_get(v___x_3042_, 2);
v_postponed_3045_ = lean_ctor_get(v___x_3042_, 3);
v_diag_3046_ = lean_ctor_get(v___x_3042_, 4);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3042_, 1);
lean_dec(v_unused_3058_);
v___x_3048_ = v___x_3042_;
v_isShared_3049_ = v_isSharedCheck_3057_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_diag_3046_);
lean_inc(v_postponed_3045_);
lean_inc(v_zetaDeltaFVarIds_3044_);
lean_inc(v_mctx_3043_);
lean_dec(v___x_3042_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3057_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 1, v___x_2906_);
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_mctx_3043_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_zetaDeltaFVarIds_3044_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_postponed_3045_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_diag_3046_);
v___x_3051_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_st_ref_put(v___y_2826_, v___x_3051_);
if (v_isShared_3025_ == 0)
{
lean_ctor_set(v___x_3024_, 0, v___x_3004_);
v___x_3054_ = v___x_3024_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3004_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2823_);
return v___x_3022_;
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3010_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
v_a_3067_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3011_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3011_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_a_3008_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
v_a_3075_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3009_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3009_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_dec(v_a_2997_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
return v___x_3006_;
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_a_2997_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
v_a_3083_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3002_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3002_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_2994_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3091_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_2996_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_2996_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3099_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_2993_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_2993_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec_ref(v___x_2989_);
lean_dec_ref(v___x_2987_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3107_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_2990_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_2990_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3112_; 
if (v_isShared_3110_ == 0)
{
v___x_3112_ = v___x_3109_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
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
lean_dec(v_a_2919_);
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_a_2915_);
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3132_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_2916_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_2916_);
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
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3140_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_2914_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_2914_);
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
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2878_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec_ref(v___x_2813_);
v_a_3148_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_2912_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_2912_);
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
}
}
}
}
}
else
{
lean_dec(v_a_2868_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
lean_dec(v_a_2863_);
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
v_a_3167_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___x_2864_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_2864_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
v_a_3175_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_2862_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_2862_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec_ref(v___x_2855_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2852_);
lean_dec_ref(v___x_2846_);
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
v_a_3183_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_2858_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_2858_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_del_object(v___x_2840_);
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v___x_2811_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v___x_2805_);
v_a_3191_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_2843_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_2843_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v_fs_2824_);
lean_dec(v_brecOnEqName_2823_);
lean_dec(v_brecOnName_2821_);
lean_dec(v___x_2820_);
lean_dec(v_levelParams_2819_);
lean_dec(v_brecOnGoName_2818_);
lean_dec_ref(v___x_2813_);
lean_dec_ref(v___x_2812_);
lean_dec_ref(v___x_2811_);
lean_dec_ref(v___x_2807_);
lean_dec_ref(v___x_2805_);
lean_dec(v___x_2802_);
v_a_3201_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_2836_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_2836_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3209_ = _args[0];
lean_object* v_tail_3210_ = _args[1];
lean_object* v_recName_3211_ = _args[2];
lean_object* v___x_3212_ = _args[3];
lean_object* v___x_3213_ = _args[4];
lean_object* v___x_3214_ = _args[5];
lean_object* v___x_3215_ = _args[6];
lean_object* v___x_3216_ = _args[7];
lean_object* v___x_3217_ = _args[8];
lean_object* v___x_3218_ = _args[9];
lean_object* v___x_3219_ = _args[10];
lean_object* v___x_3220_ = _args[11];
lean_object* v___x_3221_ = _args[12];
lean_object* v___x_3222_ = _args[13];
lean_object* v_val_3223_ = _args[14];
lean_object* v___x_3224_ = _args[15];
lean_object* v_brecOnGoName_3225_ = _args[16];
lean_object* v_levelParams_3226_ = _args[17];
lean_object* v___x_3227_ = _args[18];
lean_object* v_brecOnName_3228_ = _args[19];
lean_object* v___x_3229_ = _args[20];
lean_object* v_brecOnEqName_3230_ = _args[21];
lean_object* v_fs_3231_ = _args[22];
lean_object* v___y_3232_ = _args[23];
lean_object* v___y_3233_ = _args[24];
lean_object* v___y_3234_ = _args[25];
lean_object* v___y_3235_ = _args[26];
lean_object* v___y_3236_ = _args[27];
_start:
{
uint8_t v___x_30655__boxed_3237_; lean_object* v_res_3238_; 
v___x_30655__boxed_3237_ = lean_unbox(v___x_3224_);
v_res_3238_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3209_, v_tail_3210_, v_recName_3211_, v___x_3212_, v___x_3213_, v___x_3214_, v___x_3215_, v___x_3216_, v___x_3217_, v___x_3218_, v___x_3219_, v___x_3220_, v___x_3221_, v___x_3222_, v_val_3223_, v___x_30655__boxed_3237_, v_brecOnGoName_3225_, v_levelParams_3226_, v___x_3227_, v_brecOnName_3228_, v___x_3229_, v_brecOnEqName_3230_, v_fs_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___x_3229_);
lean_dec(v_val_3223_);
lean_dec_ref(v___x_3222_);
lean_dec(v___x_3221_);
lean_dec_ref(v___x_3217_);
lean_dec(v___x_3216_);
lean_dec(v___x_3215_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(lean_object* v_targs_3239_, lean_object* v_a_3240_, uint8_t v___x_3241_, lean_object* v_f_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; 
lean_inc_ref(v_targs_3239_);
v___x_3248_ = lean_array_push(v_targs_3239_, v_f_3242_);
v___x_3249_ = l_Lean_mkAppN(v_a_3240_, v_targs_3239_);
lean_dec_ref(v_targs_3239_);
v___x_3250_ = 0;
v___x_3251_ = 1;
v___x_3252_ = l_Lean_Meta_mkForallFVars(v___x_3248_, v___x_3249_, v___x_3250_, v___x_3241_, v___x_3241_, v___x_3251_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec_ref(v___x_3248_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed(lean_object* v_targs_3253_, lean_object* v_a_3254_, lean_object* v___x_3255_, lean_object* v_f_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v___x_31369__boxed_3262_; lean_object* v_res_3263_; 
v___x_31369__boxed_3262_ = lean_unbox(v___x_3255_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0(v_targs_3253_, v_a_3254_, v___x_31369__boxed_3262_, v_f_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(lean_object* v_a_3267_, uint8_t v___x_3268_, lean_object* v___x_3269_, lean_object* v_targs_3270_, lean_object* v_x_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3277_ = lean_box(v___x_3268_);
lean_inc_ref(v_targs_3270_);
v___f_3278_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3278_, 0, v_targs_3270_);
lean_closure_set(v___f_3278_, 1, v_a_3267_);
lean_closure_set(v___f_3278_, 2, v___x_3277_);
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___closed__1));
v___x_3280_ = l_Lean_mkAppN(v___x_3269_, v_targs_3270_);
lean_dec_ref(v_targs_3270_);
v___x_3281_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3279_, v___x_3280_, v___f_3278_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed(lean_object* v_a_3282_, lean_object* v___x_3283_, lean_object* v___x_3284_, lean_object* v_targs_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v___x_31403__boxed_3292_; lean_object* v_res_3293_; 
v___x_31403__boxed_3292_ = lean_unbox(v___x_3283_);
v_res_3293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1(v_a_3282_, v___x_31403__boxed_3292_, v___x_3284_, v_targs_3285_, v_x_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec_ref(v_x_3286_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(lean_object* v_a_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_a_3294_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed(lean_object* v_a_3302_, lean_object* v_x_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2(v_a_3302_, v_x_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v_x_3303_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v___x_3311_, lean_object* v___x_3312_, lean_object* v_as_3313_, size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_b_3316_);
return v___x_3323_;
}
else
{
lean_object* v_snd_3324_; lean_object* v_fst_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3422_; 
v_snd_3324_ = lean_ctor_get(v_b_3316_, 1);
v_fst_3325_ = lean_ctor_get(v_b_3316_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_b_3316_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3327_ = v_b_3316_;
v_isShared_3328_ = v_isSharedCheck_3422_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_snd_3324_);
lean_inc(v_fst_3325_);
lean_dec(v_b_3316_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3422_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_fst_3329_; lean_object* v_snd_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3421_; 
v_fst_3329_ = lean_ctor_get(v_snd_3324_, 0);
v_snd_3330_ = lean_ctor_get(v_snd_3324_, 1);
v_isSharedCheck_3421_ = !lean_is_exclusive(v_snd_3324_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3332_ = v_snd_3324_;
v_isShared_3333_ = v_isSharedCheck_3421_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_snd_3330_);
lean_inc(v_fst_3329_);
lean_dec(v_snd_3324_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3421_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_next_3342_; 
v_next_3342_ = lean_ctor_get(v_snd_3330_, 0);
lean_inc(v_next_3342_);
if (lean_obj_tag(v_next_3342_) == 0)
{
goto v___jp_3334_;
}
else
{
lean_object* v_upperBound_3343_; lean_object* v_val_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3420_; 
v_upperBound_3343_ = lean_ctor_get(v_snd_3330_, 1);
v_val_3344_ = lean_ctor_get(v_next_3342_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v_next_3342_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3346_ = v_next_3342_;
v_isShared_3347_ = v_isSharedCheck_3420_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_val_3344_);
lean_dec(v_next_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3420_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
uint8_t v___x_3348_; 
v___x_3348_ = lean_nat_dec_lt(v_val_3344_, v_upperBound_3343_);
if (v___x_3348_ == 0)
{
lean_del_object(v___x_3346_);
lean_dec(v_val_3344_);
goto v___jp_3334_;
}
else
{
lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3417_; 
lean_inc(v_upperBound_3343_);
lean_del_object(v___x_3332_);
lean_del_object(v___x_3327_);
v_isSharedCheck_3417_ = !lean_is_exclusive(v_snd_3330_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3418_ = lean_ctor_get(v_snd_3330_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_snd_3330_, 0);
lean_dec(v_unused_3419_);
v___x_3350_ = v_snd_3330_;
v_isShared_3351_ = v_isSharedCheck_3417_;
goto v_resetjp_3349_;
}
else
{
lean_dec(v_snd_3330_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3417_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_array_3352_; lean_object* v_start_3353_; lean_object* v_stop_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v_array_3352_ = lean_ctor_get(v_fst_3329_, 0);
v_start_3353_ = lean_ctor_get(v_fst_3329_, 1);
v_stop_3354_ = lean_ctor_get(v_fst_3329_, 2);
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_nat_add(v_val_3344_, v___x_3355_);
lean_dec(v_val_3344_);
lean_inc(v___x_3356_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3356_);
v___x_3358_ = v___x_3346_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3358_);
v___x_3360_ = v___x_3350_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_upperBound_3343_);
v___x_3360_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
uint8_t v___x_3361_; 
v___x_3361_ = lean_nat_dec_lt(v_start_3353_, v_stop_3354_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec(v___x_3356_);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v_fst_3329_);
lean_ctor_set(v___x_3362_, 1, v___x_3360_);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_fst_3325_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
else
{
lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3411_; 
lean_inc(v_stop_3354_);
lean_inc(v_start_3353_);
lean_inc_ref(v_array_3352_);
v_isSharedCheck_3411_ = !lean_is_exclusive(v_fst_3329_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; lean_object* v_unused_3413_; lean_object* v_unused_3414_; 
v_unused_3412_ = lean_ctor_get(v_fst_3329_, 2);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_fst_3329_, 1);
lean_dec(v_unused_3413_);
v_unused_3414_ = lean_ctor_get(v_fst_3329_, 0);
lean_dec(v_unused_3414_);
v___x_3366_ = v_fst_3329_;
v_isShared_3367_ = v_isSharedCheck_3411_;
goto v_resetjp_3365_;
}
else
{
lean_dec(v_fst_3329_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3411_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
uint8_t v___x_3368_; lean_object* v_a_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3368_ = lean_nat_dec_lt(v___x_3311_, v___x_3312_);
v_a_3369_ = lean_array_uget_borrowed(v_as_3313_, v_i_3315_);
v___x_3370_ = lean_array_fget_borrowed(v_array_3352_, v_start_3353_);
v___x_3371_ = lean_box(v___x_3368_);
lean_inc(v___x_3370_);
lean_inc(v_a_3369_);
v___f_3372_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3372_, 0, v_a_3369_);
lean_closure_set(v___f_3372_, 1, v___x_3371_);
lean_closure_set(v___f_3372_, 2, v___x_3370_);
v___x_3373_ = lean_nat_add(v_start_3353_, v___x_3355_);
lean_dec(v_start_3353_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 1, v___x_3373_);
v___x_3375_ = v___x_3366_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_array_3352_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_stop_3354_);
v___x_3375_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; 
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
lean_inc(v_a_3369_);
v___x_3376_ = lean_infer_type(v_a_3369_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = 0;
v___x_3379_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3377_, v___f_3372_, v___x_3378_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; size_t v___x_3391_; size_t v___x_3392_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___f_3381_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3381_, 0, v_a_3380_);
v___x_3382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___closed__0));
v___x_3383_ = l_Nat_reprFast(v___x_3356_);
v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
lean_dec_ref(v___x_3383_);
v___x_3385_ = lean_box(0);
v___x_3386_ = l_Lean_Name_str___override(v___x_3385_, v___x_3384_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___f_3381_);
v___x_3388_ = lean_array_push(v_fst_3325_, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3375_);
lean_ctor_set(v___x_3389_, 1, v___x_3360_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = ((size_t)1ULL);
v___x_3392_ = lean_usize_add(v_i_3315_, v___x_3391_);
v_i_3315_ = v___x_3392_;
v_b_3316_ = v___x_3390_;
goto _start;
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___x_3360_);
lean_dec(v___x_3356_);
lean_dec(v_fst_3325_);
v_a_3394_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3379_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3379_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_3375_);
lean_dec_ref(v___f_3372_);
lean_dec_ref(v___x_3360_);
lean_dec(v___x_3356_);
lean_dec(v_fst_3325_);
v_a_3402_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3376_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3376_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
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
v___jp_3334_:
{
lean_object* v___x_3336_; 
if (v_isShared_3333_ == 0)
{
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_fst_3329_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_snd_3330_);
v___x_3336_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3336_);
v___x_3338_ = v___x_3327_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fst_3325_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v___x_3423_, lean_object* v___x_3424_, lean_object* v_as_3425_, lean_object* v_sz_3426_, lean_object* v_i_3427_, lean_object* v_b_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
size_t v_sz_boxed_3434_; size_t v_i_boxed_3435_; lean_object* v_res_3436_; 
v_sz_boxed_3434_ = lean_unbox_usize(v_sz_3426_);
lean_dec(v_sz_3426_);
v_i_boxed_3435_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3423_, v___x_3424_, v_as_3425_, v_sz_boxed_3434_, v_i_boxed_3435_, v_b_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v_as_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3423_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3437_, size_t v_i_3438_, lean_object* v_bs_3439_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_lt(v_i_3438_, v_sz_3437_);
if (v___x_3440_ == 0)
{
return v_bs_3439_;
}
else
{
lean_object* v_v_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3459_; 
v_v_3441_ = lean_array_uget(v_bs_3439_, v_i_3438_);
v_fst_3442_ = lean_ctor_get(v_v_3441_, 0);
v_snd_3443_ = lean_ctor_get(v_v_3441_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_v_3441_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3445_ = v_v_3441_;
v_isShared_3446_ = v_isSharedCheck_3459_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_snd_3443_);
lean_inc(v_fst_3442_);
lean_dec(v_v_3441_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3459_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v_bs_x27_3448_; uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v_bs_x27_3448_ = lean_array_uset(v_bs_3439_, v_i_3438_, v___x_3447_);
v___x_3449_ = 0;
v___x_3450_ = lean_box(v___x_3449_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3450_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_snd_3443_);
v___x_3452_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v_fst_3442_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3438_, v___x_3454_);
v___x_3456_ = lean_array_uset(v_bs_x27_3448_, v_i_3438_, v___x_3453_);
v_i_3438_ = v___x_3455_;
v_bs_3439_ = v___x_3456_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3460_, lean_object* v_i_3461_, lean_object* v_bs_3462_){
_start:
{
size_t v_sz_boxed_3463_; size_t v_i_boxed_3464_; lean_object* v_res_3465_; 
v_sz_boxed_3463_ = lean_unbox_usize(v_sz_3460_);
lean_dec(v_sz_3460_);
v_i_boxed_3464_ = lean_unbox_usize(v_i_3461_);
lean_dec(v_i_3461_);
v_res_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3463_, v_i_boxed_3464_, v_bs_3462_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3466_, lean_object* v___x_3467_, lean_object* v_a_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v___x_30198__overap_3474_; lean_object* v___x_3475_; 
v___x_30198__overap_3474_ = l_instInhabitedOfMonad___redArg(v___x_3466_, v___x_3467_);
lean_inc(v___y_3472_);
lean_inc_ref(v___y_3471_);
lean_inc(v___y_3470_);
lean_inc_ref(v___y_3469_);
v___x_3475_ = lean_apply_5(v___x_30198__overap_3474_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, lean_box(0));
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3476_, lean_object* v___x_3477_, lean_object* v_a_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3476_, v___x_3477_, v_a_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3485_; 
v___x_3485_ = l_instMonadEIO___redArg();
return v___x_3485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3487_ = l_StateRefT_x27_instMonad___redArg(v___x_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3492_, lean_object* v_declInfos_3493_, lean_object* v_k_3494_, lean_object* v_kind_3495_, lean_object* v_b_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v_kind_boxed_3502_; lean_object* v_res_3503_; 
v_kind_boxed_3502_ = lean_unbox(v_kind_3495_);
v_res_3503_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3492_, v_declInfos_3493_, v_k_3494_, v_kind_boxed_3502_, v_b_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3504_, lean_object* v_declInfos_3505_, lean_object* v_k_3506_, uint8_t v_kind_3507_, lean_object* v_name_3508_, uint8_t v_bi_3509_, lean_object* v_type_3510_, uint8_t v_kind_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___f_3518_; lean_object* v___x_3519_; 
v___x_3517_ = lean_box(v_kind_3507_);
v___f_3518_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3518_, 0, v_acc_3504_);
lean_closure_set(v___f_3518_, 1, v_declInfos_3505_);
lean_closure_set(v___f_3518_, 2, v_k_3506_);
lean_closure_set(v___f_3518_, 3, v___x_3517_);
v___x_3519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3508_, v_bi_3509_, v_type_3510_, v___f_3518_, v_kind_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
v_a_3528_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3519_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3519_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3536_, lean_object* v_k_3537_, uint8_t v_kind_3538_, lean_object* v_acc_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v_toApplicative_3546_; lean_object* v_toFunctor_3547_; lean_object* v_toSeq_3548_; lean_object* v_toSeqLeft_3549_; lean_object* v_toSeqRight_3550_; lean_object* v___f_3551_; lean_object* v___f_3552_; lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; lean_object* v___f_3556_; lean_object* v___f_3557_; lean_object* v___f_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v_toApplicative_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3618_; 
v___x_3545_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3546_ = lean_ctor_get(v___x_3545_, 0);
v_toFunctor_3547_ = lean_ctor_get(v_toApplicative_3546_, 0);
v_toSeq_3548_ = lean_ctor_get(v_toApplicative_3546_, 2);
v_toSeqLeft_3549_ = lean_ctor_get(v_toApplicative_3546_, 3);
v_toSeqRight_3550_ = lean_ctor_get(v_toApplicative_3546_, 4);
v___f_3551_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3552_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3547_, 2);
v___f_3553_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3553_, 0, v_toFunctor_3547_);
v___f_3554_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3554_, 0, v_toFunctor_3547_);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___f_3553_);
lean_ctor_set(v___x_3555_, 1, v___f_3554_);
lean_inc(v_toSeqRight_3550_);
v___f_3556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3556_, 0, v_toSeqRight_3550_);
lean_inc(v_toSeqLeft_3549_);
v___f_3557_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3557_, 0, v_toSeqLeft_3549_);
lean_inc(v_toSeq_3548_);
v___f_3558_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3558_, 0, v_toSeq_3548_);
v___x_3559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3555_);
lean_ctor_set(v___x_3559_, 1, v___f_3551_);
lean_ctor_set(v___x_3559_, 2, v___f_3558_);
lean_ctor_set(v___x_3559_, 3, v___f_3557_);
lean_ctor_set(v___x_3559_, 4, v___f_3556_);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v___f_3552_);
v___x_3561_ = l_StateRefT_x27_instMonad___redArg(v___x_3560_);
v_toApplicative_3562_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; 
v_unused_3619_ = lean_ctor_get(v___x_3561_, 1);
lean_dec(v_unused_3619_);
v___x_3564_ = v___x_3561_;
v_isShared_3565_ = v_isSharedCheck_3618_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_toApplicative_3562_);
lean_dec(v___x_3561_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3618_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v_toFunctor_3566_; lean_object* v_toSeq_3567_; lean_object* v_toSeqLeft_3568_; lean_object* v_toSeqRight_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3616_; 
v_toFunctor_3566_ = lean_ctor_get(v_toApplicative_3562_, 0);
v_toSeq_3567_ = lean_ctor_get(v_toApplicative_3562_, 2);
v_toSeqLeft_3568_ = lean_ctor_get(v_toApplicative_3562_, 3);
v_toSeqRight_3569_ = lean_ctor_get(v_toApplicative_3562_, 4);
v_isSharedCheck_3616_ = !lean_is_exclusive(v_toApplicative_3562_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_toApplicative_3562_, 1);
lean_dec(v_unused_3617_);
v___x_3571_ = v_toApplicative_3562_;
v_isShared_3572_ = v_isSharedCheck_3616_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_toSeqRight_3569_);
lean_inc(v_toSeqLeft_3568_);
lean_inc(v_toSeq_3567_);
lean_inc(v_toFunctor_3566_);
lean_dec(v_toApplicative_3562_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3616_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___f_3573_; lean_object* v___f_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___x_3582_; 
v___f_3573_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3574_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3566_);
v___f_3575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3575_, 0, v_toFunctor_3566_);
v___f_3576_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3576_, 0, v_toFunctor_3566_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___f_3575_);
lean_ctor_set(v___x_3577_, 1, v___f_3576_);
v___f_3578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3578_, 0, v_toSeqRight_3569_);
v___f_3579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3579_, 0, v_toSeqLeft_3568_);
v___f_3580_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3580_, 0, v_toSeq_3567_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 4, v___f_3578_);
lean_ctor_set(v___x_3571_, 3, v___f_3579_);
lean_ctor_set(v___x_3571_, 2, v___f_3580_);
lean_ctor_set(v___x_3571_, 1, v___f_3573_);
lean_ctor_set(v___x_3571_, 0, v___x_3577_);
v___x_3582_ = v___x_3571_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3615_, 1, v___f_3573_);
lean_ctor_set(v_reuseFailAlloc_3615_, 2, v___f_3580_);
lean_ctor_set(v_reuseFailAlloc_3615_, 3, v___f_3579_);
lean_ctor_set(v_reuseFailAlloc_3615_, 4, v___f_3578_);
v___x_3582_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___f_3574_);
lean_ctor_set(v___x_3564_, 0, v___x_3582_);
v___x_3584_ = v___x_3564_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v___f_3574_);
v___x_3584_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3585_ = lean_array_get_size(v_acc_3539_);
v___x_3586_ = lean_array_get_size(v_declInfos_3536_);
v___x_3587_ = lean_nat_dec_lt(v___x_3585_, v___x_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v___x_3584_);
lean_dec_ref(v_declInfos_3536_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
v___x_3588_ = lean_apply_6(v_k_3537_, v_acc_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, lean_box(0));
return v___x_3588_;
}
else
{
lean_object* v___x_3589_; uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_snd_3598_; lean_object* v_fst_3599_; lean_object* v_fst_3600_; lean_object* v_snd_3601_; lean_object* v___x_3602_; 
v___x_3589_ = lean_box(0);
v___x_3590_ = 0;
v___x_3591_ = l_Lean_instInhabitedExpr;
v___f_3592_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3592_, 0, v___x_3584_);
lean_closure_set(v___f_3592_, 1, v___x_3591_);
v___f_3593_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3593_, 0, v___f_3592_);
v___x_3594_ = lean_box(v___x_3590_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___f_3593_);
v___x_3596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3589_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_array_get(v___x_3596_, v_declInfos_3536_, v___x_3585_);
lean_dec_ref_known(v___x_3596_, 2);
v_snd_3598_ = lean_ctor_get(v___x_3597_, 1);
lean_inc(v_snd_3598_);
v_fst_3599_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_fst_3599_);
lean_dec(v___x_3597_);
v_fst_3600_ = lean_ctor_get(v_snd_3598_, 0);
lean_inc(v_fst_3600_);
v_snd_3601_ = lean_ctor_get(v_snd_3598_, 1);
lean_inc(v_snd_3601_);
lean_dec(v_snd_3598_);
lean_inc(v___y_3543_);
lean_inc_ref(v___y_3542_);
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc_ref(v_acc_3539_);
v___x_3602_ = lean_apply_6(v_snd_3601_, v_acc_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, lean_box(0));
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = lean_unbox(v_fst_3600_);
lean_dec(v_fst_3600_);
v___x_3605_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3539_, v_declInfos_3536_, v_k_3537_, v_kind_3538_, v_fst_3599_, v___x_3604_, v_a_3603_, v_kind_3538_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3605_;
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v_fst_3600_);
lean_dec(v_fst_3599_);
lean_dec_ref(v_acc_3539_);
lean_dec_ref(v_k_3537_);
lean_dec_ref(v_declInfos_3536_);
v_a_3606_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3602_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3602_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3620_, lean_object* v_declInfos_3621_, lean_object* v_k_3622_, uint8_t v_kind_3623_, lean_object* v_b_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_array_push(v_acc_3620_, v_b_3624_);
v___x_3631_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3621_, v_k_3622_, v_kind_3623_, v___x_3630_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3632_, lean_object* v_declInfos_3633_, lean_object* v_k_3634_, lean_object* v_kind_3635_, lean_object* v_name_3636_, lean_object* v_bi_3637_, lean_object* v_type_3638_, lean_object* v_kind_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
uint8_t v_kind_boxed_3645_; uint8_t v_bi_boxed_3646_; uint8_t v_kind_boxed_3647_; lean_object* v_res_3648_; 
v_kind_boxed_3645_ = lean_unbox(v_kind_3635_);
v_bi_boxed_3646_ = lean_unbox(v_bi_3637_);
v_kind_boxed_3647_ = lean_unbox(v_kind_3639_);
v_res_3648_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3632_, v_declInfos_3633_, v_k_3634_, v_kind_boxed_3645_, v_name_3636_, v_bi_boxed_3646_, v_type_3638_, v_kind_boxed_3647_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3649_, lean_object* v_k_3650_, lean_object* v_kind_3651_, lean_object* v_acc_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
uint8_t v_kind_boxed_3658_; lean_object* v_res_3659_; 
v_kind_boxed_3658_ = lean_unbox(v_kind_3651_);
v_res_3659_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3649_, v_k_3650_, v_kind_boxed_3658_, v_acc_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3660_, lean_object* v_k_3661_, uint8_t v_kind_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3660_, v_k_3661_, v_kind_3662_, v___x_3668_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3670_, lean_object* v_k_3671_, lean_object* v_kind_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v_kind_boxed_3678_; lean_object* v_res_3679_; 
v_kind_boxed_3678_ = lean_unbox(v_kind_3672_);
v_res_3679_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3670_, v_k_3671_, v_kind_boxed_3678_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3680_, lean_object* v_k_3681_, uint8_t v_kind_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
size_t v_sz_3688_; size_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_sz_3688_ = lean_array_size(v_declInfos_3680_);
v___x_3689_ = ((size_t)0ULL);
v___x_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3688_, v___x_3689_, v_declInfos_3680_);
v___x_3691_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3690_, v_k_3681_, v_kind_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3692_, lean_object* v_k_3693_, lean_object* v_kind_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
uint8_t v_kind_boxed_3700_; lean_object* v_res_3701_; 
v_kind_boxed_3700_ = lean_unbox(v_kind_3694_);
v_res_3701_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3692_, v_k_3693_, v_kind_boxed_3700_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3704_ = lean_unsigned_to_nat(4u);
v___x_3705_ = lean_unsigned_to_nat(202u);
v___x_3706_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3707_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3708_ = l_mkPanicMessageWithDecl(v___x_3707_, v___x_3706_, v___x_3705_, v___x_3704_, v___x_3703_);
return v___x_3708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3715_ = l_Lean_stringToMessageData(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3719_, lean_object* v_numMotives_3720_, lean_object* v_numMinors_3721_, lean_object* v___x_3722_, lean_object* v_all_3723_, lean_object* v___x_3724_, lean_object* v___x_3725_, lean_object* v_head_3726_, lean_object* v_tail_3727_, lean_object* v_recName_3728_, lean_object* v_brecOnGoName_3729_, lean_object* v_levelParams_3730_, lean_object* v_brecOnName_3731_, lean_object* v_brecOnEqName_3732_, lean_object* v_type_3733_, lean_object* v_refArgs_3734_, lean_object* v_refBody_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v___x_3741_ = lean_nat_add(v_nParams_3719_, v_numMotives_3720_);
v___x_3742_ = lean_nat_add(v___x_3741_, v_numMinors_3721_);
v___x_3743_ = lean_array_get_size(v_refArgs_3734_);
v___x_3744_ = lean_nat_dec_lt(v___x_3742_, v___x_3743_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v___x_3742_);
lean_dec(v___x_3741_);
lean_dec_ref(v_refArgs_3734_);
lean_dec_ref(v_type_3733_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3724_);
lean_dec_ref(v_all_3723_);
lean_dec(v___x_3722_);
lean_dec(v_nParams_3719_);
v___x_3745_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3746_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3745_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3746_;
}
else
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3747_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3719_);
lean_inc_ref_n(v_refArgs_3734_, 2);
v___x_3748_ = l_Array_toSubarray___redArg(v_refArgs_3734_, v___x_3747_, v_nParams_3719_);
lean_inc(v___x_3741_);
v___x_3749_ = l_Array_toSubarray___redArg(v_refArgs_3734_, v_nParams_3719_, v___x_3741_);
v___x_3750_ = l_Subarray_copy___redArg(v___x_3749_);
v___x_3751_ = l_Lean_Expr_getAppFn(v_refBody_3735_);
v___x_3752_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3750_, v___x_3751_);
lean_dec_ref(v___x_3751_);
if (lean_obj_tag(v___x_3752_) == 1)
{
lean_object* v_val_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___f_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec_ref(v_type_3733_);
v_val_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_val_3753_);
lean_dec_ref_known(v___x_3752_, 1);
lean_inc_n(v___x_3742_, 2);
lean_inc_ref_n(v_refArgs_3734_, 2);
v___x_3754_ = l_Array_toSubarray___redArg(v_refArgs_3734_, v___x_3741_, v___x_3742_);
v___x_3755_ = l_Subarray_copy___redArg(v___x_3748_);
v___x_3756_ = l_Subarray_copy___redArg(v___x_3754_);
v___x_3757_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v___x_3750_);
lean_inc_ref(v___x_3755_);
lean_inc(v___x_3722_);
v___f_3758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3758_, 0, v___x_3722_);
lean_closure_set(v___f_3758_, 1, v___x_3755_);
lean_closure_set(v___f_3758_, 2, v___x_3750_);
lean_closure_set(v___f_3758_, 3, v_all_3723_);
lean_closure_set(v___f_3758_, 4, v___x_3724_);
lean_closure_set(v___f_3758_, 5, v___x_3747_);
lean_closure_set(v___f_3758_, 6, v___x_3757_);
v___x_3759_ = lean_nat_sub(v___x_3743_, v___x_3757_);
lean_inc(v___x_3759_);
v___x_3760_ = l_Array_toSubarray___redArg(v_refArgs_3734_, v___x_3742_, v___x_3759_);
v___x_3761_ = l_Subarray_copy___redArg(v___x_3760_);
v___x_3762_ = lean_array_get(v___x_3725_, v_refArgs_3734_, v___x_3759_);
lean_dec(v___x_3759_);
lean_dec_ref(v_refArgs_3734_);
lean_inc(v___y_3739_);
lean_inc_ref(v___y_3738_);
lean_inc(v___y_3737_);
lean_inc_ref(v___y_3736_);
lean_inc(v___x_3762_);
v___x_3763_ = lean_infer_type(v___x_3762_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3765_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
lean_inc(v___y_3739_);
lean_inc_ref(v___y_3738_);
lean_inc(v___y_3737_);
lean_inc_ref(v___y_3736_);
v___x_3765_ = lean_infer_type(v_a_3764_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3767_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
lean_inc(v_a_3766_);
lean_dec_ref_known(v___x_3765_, 1);
v___x_3767_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3766_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
if (lean_obj_tag(v_a_3768_) == 1)
{
lean_object* v_val_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___f_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; size_t v_sz_3782_; size_t v___x_3783_; lean_object* v___x_3784_; 
v_val_3769_ = lean_ctor_get(v_a_3768_, 0);
lean_inc(v_val_3769_);
lean_dec_ref_known(v_a_3768_, 1);
v___x_3770_ = l_Lean_mkLevelMax(v_val_3769_, v_head_3726_);
v___x_3771_ = lean_array_get_size(v___x_3750_);
v___x_3772_ = l_Array_ofFn___redArg(v___x_3771_, v___f_3758_);
v___x_3773_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3774_ = lean_array_get_size(v___x_3772_);
lean_inc_ref(v___x_3772_);
v___x_3775_ = l_Array_toSubarray___redArg(v___x_3772_, v___x_3747_, v___x_3774_);
v___x_3776_ = lean_box(v___x_3744_);
lean_inc(v___x_3742_);
lean_inc_ref(v___x_3750_);
lean_inc_ref(v___x_3775_);
v___f_3777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3777_, 0, v___x_3770_);
lean_closure_set(v___f_3777_, 1, v_tail_3727_);
lean_closure_set(v___f_3777_, 2, v_recName_3728_);
lean_closure_set(v___f_3777_, 3, v___x_3755_);
lean_closure_set(v___f_3777_, 4, v___x_3775_);
lean_closure_set(v___f_3777_, 5, v___x_3750_);
lean_closure_set(v___f_3777_, 6, v___x_3742_);
lean_closure_set(v___f_3777_, 7, v___x_3743_);
lean_closure_set(v___f_3777_, 8, v___x_3756_);
lean_closure_set(v___f_3777_, 9, v___x_3772_);
lean_closure_set(v___f_3777_, 10, v___x_3761_);
lean_closure_set(v___f_3777_, 11, v___x_3762_);
lean_closure_set(v___f_3777_, 12, v___x_3757_);
lean_closure_set(v___f_3777_, 13, v___x_3725_);
lean_closure_set(v___f_3777_, 14, v_val_3753_);
lean_closure_set(v___f_3777_, 15, v___x_3776_);
lean_closure_set(v___f_3777_, 16, v_brecOnGoName_3729_);
lean_closure_set(v___f_3777_, 17, v_levelParams_3730_);
lean_closure_set(v___f_3777_, 18, v___x_3722_);
lean_closure_set(v___f_3777_, 19, v_brecOnName_3731_);
lean_closure_set(v___f_3777_, 20, v___x_3747_);
lean_closure_set(v___f_3777_, 21, v_brecOnEqName_3732_);
v___x_3778_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
lean_ctor_set(v___x_3779_, 1, v___x_3771_);
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3775_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3773_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v_sz_3782_ = lean_array_size(v___x_3750_);
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v___x_3742_, v___x_3743_, v___x_3750_, v_sz_3782_, v___x_3783_, v___x_3781_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3742_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v_fst_3786_; uint8_t v___x_3787_; lean_object* v___x_3788_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v_fst_3786_ = lean_ctor_get(v_a_3785_, 0);
lean_inc(v_fst_3786_);
lean_dec(v_a_3785_);
v___x_3787_ = 0;
v___x_3788_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3786_, v___f_3777_, v___x_3787_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3788_;
}
else
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec_ref(v___f_3777_);
v_a_3789_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3784_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3784_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_dec(v_a_3768_);
lean_dec_ref(v___x_3761_);
lean_dec_ref(v___f_3758_);
lean_dec_ref(v___x_3756_);
lean_dec_ref(v___x_3755_);
lean_dec(v_val_3753_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3742_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3722_);
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3798_ = l_Lean_MessageData_ofExpr(v___x_3762_);
v___x_3799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3797_);
lean_ctor_set(v___x_3799_, 1, v___x_3798_);
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3799_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3801_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3802_;
}
}
else
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3810_; 
lean_dec(v___x_3762_);
lean_dec_ref(v___x_3761_);
lean_dec_ref(v___f_3758_);
lean_dec_ref(v___x_3756_);
lean_dec_ref(v___x_3755_);
lean_dec(v_val_3753_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3742_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3722_);
v_a_3803_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3805_ = v___x_3767_;
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3767_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3810_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3808_; 
if (v_isShared_3806_ == 0)
{
v___x_3808_ = v___x_3805_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec(v___x_3762_);
lean_dec_ref(v___x_3761_);
lean_dec_ref(v___f_3758_);
lean_dec_ref(v___x_3756_);
lean_dec_ref(v___x_3755_);
lean_dec(v_val_3753_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3742_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3722_);
v_a_3811_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3765_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3765_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v___x_3762_);
lean_dec_ref(v___x_3761_);
lean_dec_ref(v___f_3758_);
lean_dec_ref(v___x_3756_);
lean_dec_ref(v___x_3755_);
lean_dec(v_val_3753_);
lean_dec_ref(v___x_3750_);
lean_dec(v___x_3742_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3722_);
v_a_3819_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3763_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3763_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3819_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec(v___x_3752_);
lean_dec_ref(v___x_3748_);
lean_dec(v___x_3742_);
lean_dec(v___x_3741_);
lean_dec_ref(v_refArgs_3734_);
lean_dec(v_brecOnEqName_3732_);
lean_dec(v_brecOnName_3731_);
lean_dec(v_levelParams_3730_);
lean_dec(v_brecOnGoName_3729_);
lean_dec(v_recName_3728_);
lean_dec(v_tail_3727_);
lean_dec(v_head_3726_);
lean_dec_ref(v___x_3725_);
lean_dec(v___x_3724_);
lean_dec_ref(v_all_3723_);
lean_dec(v___x_3722_);
v___x_3827_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3828_ = l_Lean_MessageData_ofExpr(v_type_3733_);
v___x_3829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3827_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3829_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___x_3832_ = lean_array_to_list(v___x_3750_);
v___x_3833_ = lean_box(0);
v___x_3834_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3832_, v___x_3833_);
v___x_3835_ = l_Lean_MessageData_ofList(v___x_3834_);
v___x_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3831_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3836_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3838_ = _args[0];
lean_object* v_numMotives_3839_ = _args[1];
lean_object* v_numMinors_3840_ = _args[2];
lean_object* v___x_3841_ = _args[3];
lean_object* v_all_3842_ = _args[4];
lean_object* v___x_3843_ = _args[5];
lean_object* v___x_3844_ = _args[6];
lean_object* v_head_3845_ = _args[7];
lean_object* v_tail_3846_ = _args[8];
lean_object* v_recName_3847_ = _args[9];
lean_object* v_brecOnGoName_3848_ = _args[10];
lean_object* v_levelParams_3849_ = _args[11];
lean_object* v_brecOnName_3850_ = _args[12];
lean_object* v_brecOnEqName_3851_ = _args[13];
lean_object* v_type_3852_ = _args[14];
lean_object* v_refArgs_3853_ = _args[15];
lean_object* v_refBody_3854_ = _args[16];
lean_object* v___y_3855_ = _args[17];
lean_object* v___y_3856_ = _args[18];
lean_object* v___y_3857_ = _args[19];
lean_object* v___y_3858_ = _args[20];
lean_object* v___y_3859_ = _args[21];
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3838_, v_numMotives_3839_, v_numMinors_3840_, v___x_3841_, v_all_3842_, v___x_3843_, v___x_3844_, v_head_3845_, v_tail_3846_, v_recName_3847_, v_brecOnGoName_3848_, v_levelParams_3849_, v_brecOnName_3850_, v_brecOnEqName_3851_, v_type_3852_, v_refArgs_3853_, v_refBody_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec_ref(v_refBody_3854_);
lean_dec(v_numMinors_3840_);
lean_dec(v_numMotives_3839_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3863_, lean_object* v_nParams_3864_, lean_object* v_all_3865_, lean_object* v_brecOnName_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v_brecOnGoName_3875_; lean_object* v___x_3876_; lean_object* v_brecOnEqName_3877_; lean_object* v___x_3878_; 
v___x_3872_ = l_Lean_instInhabitedExpr;
v___x_3873_ = lean_box(0);
v___x_3874_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3866_, 2);
v_brecOnGoName_3875_ = l_Lean_Name_str___override(v_brecOnName_3866_, v___x_3874_);
v___x_3876_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3877_ = l_Lean_Name_str___override(v_brecOnName_3866_, v___x_3876_);
lean_inc(v_recName_3863_);
v___x_3878_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3863_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3906_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3881_ = v___x_3878_;
v_isShared_3882_ = v_isSharedCheck_3906_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3878_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3906_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
if (lean_obj_tag(v_a_3879_) == 7)
{
lean_object* v_val_3883_; lean_object* v_toConstantVal_3884_; lean_object* v_numMotives_3885_; lean_object* v_numMinors_3886_; lean_object* v_levelParams_3887_; lean_object* v_type_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_del_object(v___x_3881_);
v_val_3883_ = lean_ctor_get(v_a_3879_, 0);
lean_inc_ref(v_val_3883_);
lean_dec_ref_known(v_a_3879_, 1);
v_toConstantVal_3884_ = lean_ctor_get(v_val_3883_, 0);
lean_inc_ref(v_toConstantVal_3884_);
v_numMotives_3885_ = lean_ctor_get(v_val_3883_, 4);
lean_inc(v_numMotives_3885_);
v_numMinors_3886_ = lean_ctor_get(v_val_3883_, 5);
lean_inc(v_numMinors_3886_);
lean_dec_ref(v_val_3883_);
v_levelParams_3887_ = lean_ctor_get(v_toConstantVal_3884_, 1);
lean_inc_n(v_levelParams_3887_, 2);
v_type_3888_ = lean_ctor_get(v_toConstantVal_3884_, 2);
lean_inc_ref(v_type_3888_);
lean_dec_ref(v_toConstantVal_3884_);
v___x_3889_ = lean_box(0);
v___x_3890_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3887_, v___x_3889_);
if (lean_obj_tag(v___x_3890_) == 1)
{
lean_object* v_head_3891_; lean_object* v_tail_3892_; lean_object* v___f_3893_; uint8_t v___x_3894_; lean_object* v___x_3895_; 
v_head_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_head_3891_);
v_tail_3892_ = lean_ctor_get(v___x_3890_, 1);
lean_inc(v_tail_3892_);
lean_inc_ref(v_type_3888_);
v___f_3893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3893_, 0, v_nParams_3864_);
lean_closure_set(v___f_3893_, 1, v_numMotives_3885_);
lean_closure_set(v___f_3893_, 2, v_numMinors_3886_);
lean_closure_set(v___f_3893_, 3, v___x_3890_);
lean_closure_set(v___f_3893_, 4, v_all_3865_);
lean_closure_set(v___f_3893_, 5, v___x_3873_);
lean_closure_set(v___f_3893_, 6, v___x_3872_);
lean_closure_set(v___f_3893_, 7, v_head_3891_);
lean_closure_set(v___f_3893_, 8, v_tail_3892_);
lean_closure_set(v___f_3893_, 9, v_recName_3863_);
lean_closure_set(v___f_3893_, 10, v_brecOnGoName_3875_);
lean_closure_set(v___f_3893_, 11, v_levelParams_3887_);
lean_closure_set(v___f_3893_, 12, v_brecOnName_3866_);
lean_closure_set(v___f_3893_, 13, v_brecOnEqName_3877_);
lean_closure_set(v___f_3893_, 14, v_type_3888_);
v___x_3894_ = 0;
v___x_3895_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3888_, v___f_3893_, v___x_3894_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
return v___x_3895_;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_dec(v___x_3890_);
lean_dec_ref(v_type_3888_);
lean_dec(v_levelParams_3887_);
lean_dec(v_numMinors_3886_);
lean_dec(v_numMotives_3885_);
lean_dec(v_brecOnEqName_3877_);
lean_dec(v_brecOnGoName_3875_);
lean_dec(v_brecOnName_3866_);
lean_dec_ref(v_all_3865_);
lean_dec(v_nParams_3864_);
v___x_3896_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3897_ = l_Lean_MessageData_ofName(v_recName_3863_);
v___x_3898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3896_);
lean_ctor_set(v___x_3898_, 1, v___x_3897_);
v___x_3899_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3898_);
lean_ctor_set(v___x_3900_, 1, v___x_3899_);
v___x_3901_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3900_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
return v___x_3901_;
}
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
lean_dec(v_a_3879_);
lean_dec(v_brecOnEqName_3877_);
lean_dec(v_brecOnGoName_3875_);
lean_dec(v_brecOnName_3866_);
lean_dec_ref(v_all_3865_);
lean_dec(v_nParams_3864_);
lean_dec(v_recName_3863_);
v___x_3902_ = lean_box(0);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 0, v___x_3902_);
v___x_3904_ = v___x_3881_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v_brecOnEqName_3877_);
lean_dec(v_brecOnGoName_3875_);
lean_dec(v_brecOnName_3866_);
lean_dec_ref(v_all_3865_);
lean_dec(v_nParams_3864_);
lean_dec(v_recName_3863_);
v_a_3907_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3878_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3878_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3915_, lean_object* v_nParams_3916_, lean_object* v_all_3917_, lean_object* v_brecOnName_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3915_, v_nParams_3916_, v_all_3917_, v_brecOnName_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3925_, lean_object* v___x_3926_, lean_object* v___x_3927_, lean_object* v___x_3928_, lean_object* v___x_3929_, lean_object* v_a_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_nat_dec_lt(v_a_3930_, v_upperBound_3925_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; 
lean_dec(v_a_3930_);
lean_dec_ref(v___x_3929_);
lean_dec(v___x_3928_);
lean_dec(v___x_3927_);
lean_dec(v___x_3926_);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_b_3931_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3939_ = lean_box(0);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_add(v_a_3930_, v___x_3940_);
lean_dec(v_a_3930_);
lean_inc_n(v___x_3941_, 2);
lean_inc(v___x_3926_);
v___x_3942_ = lean_name_append_index_after(v___x_3926_, v___x_3941_);
lean_inc(v___x_3927_);
v___x_3943_ = lean_name_append_index_after(v___x_3927_, v___x_3941_);
lean_inc_ref(v___x_3929_);
lean_inc(v___x_3928_);
v___x_3944_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3942_, v___x_3928_, v___x_3929_, v___x_3943_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_dec_ref_known(v___x_3944_, 1);
v_a_3930_ = v___x_3941_;
v_b_3931_ = v___x_3939_;
goto _start;
}
else
{
lean_dec(v___x_3941_);
lean_dec_ref(v___x_3929_);
lean_dec(v___x_3928_);
lean_dec(v___x_3927_);
lean_dec(v___x_3926_);
return v___x_3944_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3946_, lean_object* v___x_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v___x_3950_, lean_object* v_a_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3946_, v___x_3947_, v___x_3948_, v___x_3949_, v___x_3950_, v_a_3951_, v_b_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v_upperBound_3946_);
return v_res_3958_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3964_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3965_ = l_Lean_Name_append(v___x_3964_, v___x_3963_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_toCold_3972_; lean_object* v_options_3973_; lean_object* v_inheritedTraceOptions_3974_; uint8_t v_hasTrace_3975_; lean_object* v___x_3976_; 
v_toCold_3972_ = lean_ctor_get(v_a_3969_, 0);
v_options_3973_ = lean_ctor_get(v_toCold_3972_, 2);
v_inheritedTraceOptions_3974_ = lean_ctor_get(v_toCold_3972_, 11);
v_hasTrace_3975_ = lean_ctor_get_uint8(v_options_3973_, sizeof(void*)*1);
v___x_3976_ = lean_box(0);
if (v_hasTrace_3975_ == 0)
{
lean_object* v___x_3977_; 
lean_inc(v_indName_3966_);
v___x_3977_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4042_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_4042_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4042_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
if (lean_obj_tag(v_a_3978_) == 5)
{
lean_object* v_val_3982_; uint8_t v_isRec_3983_; 
v_val_3982_ = lean_ctor_get(v_a_3978_, 0);
lean_inc_ref(v_val_3982_);
lean_dec_ref_known(v_a_3978_, 1);
v_isRec_3983_ = lean_ctor_get_uint8(v_val_3982_, sizeof(void*)*6);
if (v_isRec_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v___x_3986_; 
lean_dec_ref(v_val_3982_);
lean_dec(v_indName_3966_);
v___x_3984_ = lean_box(0);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_3984_);
v___x_3986_ = v___x_3980_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
else
{
lean_object* v_toConstantVal_3988_; lean_object* v_numParams_3989_; lean_object* v_all_3990_; lean_object* v_numNested_3991_; lean_object* v_type_3992_; lean_object* v___x_3993_; 
lean_del_object(v___x_3980_);
v_toConstantVal_3988_ = lean_ctor_get(v_val_3982_, 0);
lean_inc_ref(v_toConstantVal_3988_);
v_numParams_3989_ = lean_ctor_get(v_val_3982_, 1);
lean_inc(v_numParams_3989_);
v_all_3990_ = lean_ctor_get(v_val_3982_, 3);
lean_inc(v_all_3990_);
v_numNested_3991_ = lean_ctor_get(v_val_3982_, 5);
lean_inc(v_numNested_3991_);
lean_dec_ref(v_val_3982_);
v_type_3992_ = lean_ctor_get(v_toConstantVal_3988_, 2);
lean_inc_ref(v_type_3992_);
lean_dec_ref(v_toConstantVal_3988_);
v___x_3993_ = l_Lean_Meta_isPropFormerType(v_type_3992_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4029_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4029_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4029_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
uint8_t v___x_3998_; 
v___x_3998_ = lean_unbox(v_a_3994_);
lean_dec(v_a_3994_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
lean_del_object(v___x_3996_);
lean_inc_n(v_indName_3966_, 2);
v___x_3999_ = l_Lean_mkRecName(v_indName_3966_);
v___x_4000_ = l_Lean_mkBRecOnName(v_indName_3966_);
lean_inc(v_all_3990_);
v___x_4001_ = lean_array_mk(v_all_3990_);
lean_inc(v___x_4000_);
lean_inc_ref(v___x_4001_);
lean_inc(v_numParams_3989_);
lean_inc(v___x_3999_);
v___x_4002_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3999_, v_numParams_3989_, v___x_4001_, v___x_4000_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4023_; 
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4023_ == 0)
{
lean_object* v_unused_4024_; 
v_unused_4024_ = lean_ctor_get(v___x_4002_, 0);
lean_dec(v_unused_4024_);
v___x_4004_ = v___x_4002_;
v_isShared_4005_ = v_isSharedCheck_4023_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v___x_4002_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4023_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4006_ = lean_unsigned_to_nat(0u);
v___x_4007_ = l_List_get_x21Internal___redArg(v___x_3976_, v_all_3990_, v___x_4006_);
lean_dec(v_all_3990_);
v___x_4008_ = lean_name_eq(v___x_4007_, v_indName_3966_);
lean_dec(v_indName_3966_);
lean_dec(v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
lean_dec_ref(v___x_4001_);
lean_dec(v___x_4000_);
lean_dec(v___x_3999_);
lean_dec(v_numNested_3991_);
lean_dec(v_numParams_3989_);
v___x_4009_ = lean_box(0);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4009_);
v___x_4011_ = v___x_4004_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_del_object(v___x_4004_);
v___x_4013_ = lean_box(0);
v___x_4014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_3991_, v___x_3999_, v___x_4000_, v_numParams_3989_, v___x_4001_, v___x_4006_, v___x_4013_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_numNested_3991_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4021_ == 0)
{
lean_object* v_unused_4022_; 
v_unused_4022_ = lean_ctor_get(v___x_4014_, 0);
lean_dec(v_unused_4022_);
v___x_4016_ = v___x_4014_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_dec(v___x_4014_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4013_);
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v___x_4013_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
else
{
return v___x_4014_;
}
}
}
}
else
{
lean_dec_ref(v___x_4001_);
lean_dec(v___x_4000_);
lean_dec(v___x_3999_);
lean_dec(v_numNested_3991_);
lean_dec(v_all_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_indName_3966_);
return v___x_4002_;
}
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
lean_dec(v_numNested_3991_);
lean_dec(v_all_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_indName_3966_);
v___x_4025_ = lean_box(0);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4025_);
v___x_4027_ = v___x_3996_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_numNested_3991_);
lean_dec(v_all_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_indName_3966_);
v_a_4030_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_3993_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_3993_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4040_; 
lean_dec(v_a_3978_);
lean_dec(v_indName_3966_);
v___x_4038_ = lean_box(0);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_4038_);
v___x_4040_ = v___x_3980_;
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
lean_dec(v_indName_3966_);
v_a_4043_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_3977_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_3977_);
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
else
{
lean_object* v___f_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v_a_4059_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v_a_4074_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v_a_4079_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v_a_4084_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v_a_4096_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v_a_4101_; 
lean_inc(v_indName_3966_);
v___f_4051_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4051_, 0, v_indName_3966_);
v___x_4052_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4053_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4054_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3974_, v_options_3973_, v___x_4054_);
if (v___x_4055_ == 0)
{
lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = l_Lean_trace_profiler;
v___x_4171_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3973_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v___f_4051_);
lean_inc(v_indName_3966_);
v___x_4172_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4237_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4237_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4237_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
if (lean_obj_tag(v_a_4173_) == 5)
{
lean_object* v_val_4177_; uint8_t v_isRec_4178_; 
v_val_4177_ = lean_ctor_get(v_a_4173_, 0);
lean_inc_ref(v_val_4177_);
lean_dec_ref_known(v_a_4173_, 1);
v_isRec_4178_ = lean_ctor_get_uint8(v_val_4177_, sizeof(void*)*6);
if (v_isRec_4178_ == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4181_; 
lean_dec_ref(v_val_4177_);
lean_dec(v_indName_3966_);
v___x_4179_ = lean_box(0);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4179_);
v___x_4181_ = v___x_4175_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
else
{
lean_object* v_toConstantVal_4183_; lean_object* v_numParams_4184_; lean_object* v_all_4185_; lean_object* v_numNested_4186_; lean_object* v_type_4187_; lean_object* v___x_4188_; 
lean_del_object(v___x_4175_);
v_toConstantVal_4183_ = lean_ctor_get(v_val_4177_, 0);
lean_inc_ref(v_toConstantVal_4183_);
v_numParams_4184_ = lean_ctor_get(v_val_4177_, 1);
lean_inc(v_numParams_4184_);
v_all_4185_ = lean_ctor_get(v_val_4177_, 3);
lean_inc(v_all_4185_);
v_numNested_4186_ = lean_ctor_get(v_val_4177_, 5);
lean_inc(v_numNested_4186_);
lean_dec_ref(v_val_4177_);
v_type_4187_ = lean_ctor_get(v_toConstantVal_4183_, 2);
lean_inc_ref(v_type_4187_);
lean_dec_ref(v_toConstantVal_4183_);
v___x_4188_ = l_Lean_Meta_isPropFormerType(v_type_4187_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4224_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4191_ = v___x_4188_;
v_isShared_4192_ = v_isSharedCheck_4224_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4188_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4224_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
uint8_t v___x_4193_; 
v___x_4193_ = lean_unbox(v_a_4189_);
lean_dec(v_a_4189_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
lean_del_object(v___x_4191_);
lean_inc_n(v_indName_3966_, 2);
v___x_4194_ = l_Lean_mkRecName(v_indName_3966_);
v___x_4195_ = l_Lean_mkBRecOnName(v_indName_3966_);
lean_inc(v_all_4185_);
v___x_4196_ = lean_array_mk(v_all_4185_);
lean_inc(v___x_4195_);
lean_inc_ref(v___x_4196_);
lean_inc(v_numParams_4184_);
lean_inc(v___x_4194_);
v___x_4197_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4194_, v_numParams_4184_, v___x_4196_, v___x_4195_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4218_; 
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4218_ == 0)
{
lean_object* v_unused_4219_; 
v_unused_4219_ = lean_ctor_get(v___x_4197_, 0);
lean_dec(v_unused_4219_);
v___x_4199_ = v___x_4197_;
v_isShared_4200_ = v_isSharedCheck_4218_;
goto v_resetjp_4198_;
}
else
{
lean_dec(v___x_4197_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4218_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v___x_4201_ = lean_unsigned_to_nat(0u);
v___x_4202_ = l_List_get_x21Internal___redArg(v___x_3976_, v_all_4185_, v___x_4201_);
lean_dec(v_all_4185_);
v___x_4203_ = lean_name_eq(v___x_4202_, v_indName_3966_);
lean_dec(v_indName_3966_);
lean_dec(v___x_4202_);
if (v___x_4203_ == 0)
{
lean_object* v___x_4204_; lean_object* v___x_4206_; 
lean_dec_ref(v___x_4196_);
lean_dec(v___x_4195_);
lean_dec(v___x_4194_);
lean_dec(v_numNested_4186_);
lean_dec(v_numParams_4184_);
v___x_4204_ = lean_box(0);
if (v_isShared_4200_ == 0)
{
lean_ctor_set(v___x_4199_, 0, v___x_4204_);
v___x_4206_ = v___x_4199_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4204_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_del_object(v___x_4199_);
v___x_4208_ = lean_box(0);
v___x_4209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4186_, v___x_4194_, v___x_4195_, v_numParams_4184_, v___x_4196_, v___x_4201_, v___x_4208_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_numNested_4186_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4216_ == 0)
{
lean_object* v_unused_4217_; 
v_unused_4217_ = lean_ctor_get(v___x_4209_, 0);
lean_dec(v_unused_4217_);
v___x_4211_ = v___x_4209_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_dec(v___x_4209_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4208_);
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v___x_4208_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
else
{
return v___x_4209_;
}
}
}
}
else
{
lean_dec_ref(v___x_4196_);
lean_dec(v___x_4195_);
lean_dec(v___x_4194_);
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_3966_);
return v___x_4197_;
}
}
else
{
lean_object* v___x_4220_; lean_object* v___x_4222_; 
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_3966_);
v___x_4220_ = lean_box(0);
if (v_isShared_4192_ == 0)
{
lean_ctor_set(v___x_4191_, 0, v___x_4220_);
v___x_4222_ = v___x_4191_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec(v_numNested_4186_);
lean_dec(v_all_4185_);
lean_dec(v_numParams_4184_);
lean_dec(v_indName_3966_);
v_a_4225_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4188_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4188_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
lean_dec(v_a_4173_);
lean_dec(v_indName_3966_);
v___x_4233_ = lean_box(0);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4233_);
v___x_4235_ = v___x_4175_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
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
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec(v_indName_3966_);
v_a_4238_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4172_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4172_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
goto v___jp_4103_;
}
}
else
{
goto v___jp_4103_;
}
v___jp_4056_:
{
lean_object* v___x_4060_; double v___x_4061_; double v___x_4062_; double v___x_4063_; double v___x_4064_; double v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4060_ = lean_io_mono_nanos_now();
v___x_4061_ = lean_float_of_nat(v___y_4058_);
v___x_4062_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4063_ = lean_float_div(v___x_4061_, v___x_4062_);
v___x_4064_ = lean_float_of_nat(v___x_4060_);
v___x_4065_ = lean_float_div(v___x_4064_, v___x_4062_);
v___x_4066_ = lean_box_float(v___x_4063_);
v___x_4067_ = lean_box_float(v___x_4065_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4066_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v_a_4059_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4052_, v_hasTrace_3975_, v___x_4053_, v_options_3973_, v___x_4055_, v___y_4057_, v___f_4051_, v___x_4069_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_4070_;
}
v___jp_4071_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_a_4074_);
v___y_4057_ = v___y_4072_;
v___y_4058_ = v___y_4073_;
v_a_4059_ = v___x_4075_;
goto v___jp_4056_;
}
v___jp_4076_:
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4080_, 0, v_a_4079_);
v___y_4057_ = v___y_4077_;
v___y_4058_ = v___y_4078_;
v_a_4059_ = v___x_4080_;
goto v___jp_4056_;
}
v___jp_4081_:
{
lean_object* v___x_4085_; double v___x_4086_; double v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4085_ = lean_io_get_num_heartbeats();
v___x_4086_ = lean_float_of_nat(v___y_4083_);
v___x_4087_ = lean_float_of_nat(v___x_4085_);
v___x_4088_ = lean_box_float(v___x_4086_);
v___x_4089_ = lean_box_float(v___x_4087_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_a_4084_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4052_, v_hasTrace_3975_, v___x_4053_, v_options_3973_, v___x_4055_, v___y_4082_, v___f_4051_, v___x_4091_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
return v___x_4092_;
}
v___jp_4093_:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4096_);
v___y_4082_ = v___y_4094_;
v___y_4083_ = v___y_4095_;
v_a_4084_ = v___x_4097_;
goto v___jp_4081_;
}
v___jp_4098_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_a_4101_);
v___y_4082_ = v___y_4099_;
v___y_4083_ = v___y_4100_;
v_a_4084_ = v___x_4102_;
goto v___jp_4081_;
}
v___jp_4103_:
{
lean_object* v___x_4104_; lean_object* v_a_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4104_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3970_);
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref(v___x_4104_);
v___x_4106_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4107_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3973_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3966_);
v___x_4109_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
if (lean_obj_tag(v_a_4110_) == 5)
{
lean_object* v_val_4111_; uint8_t v_isRec_4112_; 
v_val_4111_ = lean_ctor_get(v_a_4110_, 0);
lean_inc_ref(v_val_4111_);
lean_dec_ref_known(v_a_4110_, 1);
v_isRec_4112_ = lean_ctor_get_uint8(v_val_4111_, sizeof(void*)*6);
if (v_isRec_4112_ == 0)
{
lean_object* v___x_4113_; 
lean_dec_ref(v_val_4111_);
lean_dec(v_indName_3966_);
v___x_4113_ = lean_box(0);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v___x_4113_;
goto v___jp_4071_;
}
else
{
lean_object* v_toConstantVal_4114_; lean_object* v_numParams_4115_; lean_object* v_all_4116_; lean_object* v_numNested_4117_; lean_object* v_type_4118_; lean_object* v___x_4119_; 
v_toConstantVal_4114_ = lean_ctor_get(v_val_4111_, 0);
lean_inc_ref(v_toConstantVal_4114_);
v_numParams_4115_ = lean_ctor_get(v_val_4111_, 1);
lean_inc(v_numParams_4115_);
v_all_4116_ = lean_ctor_get(v_val_4111_, 3);
lean_inc(v_all_4116_);
v_numNested_4117_ = lean_ctor_get(v_val_4111_, 5);
lean_inc(v_numNested_4117_);
lean_dec_ref(v_val_4111_);
v_type_4118_ = lean_ctor_get(v_toConstantVal_4114_, 2);
lean_inc_ref(v_type_4118_);
lean_dec_ref(v_toConstantVal_4114_);
v___x_4119_ = l_Lean_Meta_isPropFormerType(v_type_4118_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; uint8_t v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = lean_unbox(v_a_4120_);
lean_dec(v_a_4120_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
lean_inc_n(v_indName_3966_, 2);
v___x_4122_ = l_Lean_mkRecName(v_indName_3966_);
v___x_4123_ = l_Lean_mkBRecOnName(v_indName_3966_);
lean_inc(v_all_4116_);
v___x_4124_ = lean_array_mk(v_all_4116_);
lean_inc(v___x_4123_);
lean_inc_ref(v___x_4124_);
lean_inc(v_numParams_4115_);
lean_inc(v___x_4122_);
v___x_4125_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4122_, v_numParams_4115_, v___x_4124_, v___x_4123_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; 
lean_dec_ref_known(v___x_4125_, 1);
v___x_4126_ = lean_unsigned_to_nat(0u);
v___x_4127_ = l_List_get_x21Internal___redArg(v___x_3976_, v_all_4116_, v___x_4126_);
lean_dec(v_all_4116_);
v___x_4128_ = lean_name_eq(v___x_4127_, v_indName_3966_);
lean_dec(v_indName_3966_);
lean_dec(v___x_4127_);
if (v___x_4128_ == 0)
{
lean_object* v___x_4129_; 
lean_dec_ref(v___x_4124_);
lean_dec(v___x_4123_);
lean_dec(v___x_4122_);
lean_dec(v_numNested_4117_);
lean_dec(v_numParams_4115_);
v___x_4129_ = lean_box(0);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v___x_4129_;
goto v___jp_4071_;
}
else
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_box(0);
v___x_4131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4117_, v___x_4122_, v___x_4123_, v_numParams_4115_, v___x_4124_, v___x_4126_, v___x_4130_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_numNested_4117_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_dec_ref_known(v___x_4131_, 1);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v___x_4130_;
goto v___jp_4071_;
}
else
{
lean_object* v_a_4132_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v___y_4077_ = v_a_4105_;
v___y_4078_ = v___x_4108_;
v_a_4079_ = v_a_4132_;
goto v___jp_4076_;
}
}
}
else
{
lean_dec_ref(v___x_4124_);
lean_dec(v___x_4123_);
lean_dec(v___x_4122_);
lean_dec(v_numNested_4117_);
lean_dec(v_all_4116_);
lean_dec(v_numParams_4115_);
lean_dec(v_indName_3966_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4133_; 
v_a_4133_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4125_, 1);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v_a_4133_;
goto v___jp_4071_;
}
else
{
lean_object* v_a_4134_; 
v_a_4134_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v___x_4125_, 1);
v___y_4077_ = v_a_4105_;
v___y_4078_ = v___x_4108_;
v_a_4079_ = v_a_4134_;
goto v___jp_4076_;
}
}
}
else
{
lean_object* v___x_4135_; 
lean_dec(v_numNested_4117_);
lean_dec(v_all_4116_);
lean_dec(v_numParams_4115_);
lean_dec(v_indName_3966_);
v___x_4135_ = lean_box(0);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v___x_4135_;
goto v___jp_4071_;
}
}
else
{
lean_object* v_a_4136_; 
lean_dec(v_numNested_4117_);
lean_dec(v_all_4116_);
lean_dec(v_numParams_4115_);
lean_dec(v_indName_3966_);
v_a_4136_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4119_, 1);
v___y_4077_ = v_a_4105_;
v___y_4078_ = v___x_4108_;
v_a_4079_ = v_a_4136_;
goto v___jp_4076_;
}
}
}
else
{
lean_object* v___x_4137_; 
lean_dec(v_a_4110_);
lean_dec(v_indName_3966_);
v___x_4137_ = lean_box(0);
v___y_4072_ = v_a_4105_;
v___y_4073_ = v___x_4108_;
v_a_4074_ = v___x_4137_;
goto v___jp_4071_;
}
}
else
{
lean_object* v_a_4138_; 
lean_dec(v_indName_3966_);
v_a_4138_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4109_, 1);
v___y_4077_ = v_a_4105_;
v___y_4078_ = v___x_4108_;
v_a_4079_ = v_a_4138_;
goto v___jp_4076_;
}
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3966_);
v___x_4140_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
if (lean_obj_tag(v_a_4141_) == 5)
{
lean_object* v_val_4142_; uint8_t v_isRec_4143_; 
v_val_4142_ = lean_ctor_get(v_a_4141_, 0);
lean_inc_ref(v_val_4142_);
lean_dec_ref_known(v_a_4141_, 1);
v_isRec_4143_ = lean_ctor_get_uint8(v_val_4142_, sizeof(void*)*6);
if (v_isRec_4143_ == 0)
{
lean_object* v___x_4144_; 
lean_dec_ref(v_val_4142_);
lean_dec(v_indName_3966_);
v___x_4144_ = lean_box(0);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v___x_4144_;
goto v___jp_4093_;
}
else
{
lean_object* v_toConstantVal_4145_; lean_object* v_numParams_4146_; lean_object* v_all_4147_; lean_object* v_numNested_4148_; lean_object* v_type_4149_; lean_object* v___x_4150_; 
v_toConstantVal_4145_ = lean_ctor_get(v_val_4142_, 0);
lean_inc_ref(v_toConstantVal_4145_);
v_numParams_4146_ = lean_ctor_get(v_val_4142_, 1);
lean_inc(v_numParams_4146_);
v_all_4147_ = lean_ctor_get(v_val_4142_, 3);
lean_inc(v_all_4147_);
v_numNested_4148_ = lean_ctor_get(v_val_4142_, 5);
lean_inc(v_numNested_4148_);
lean_dec_ref(v_val_4142_);
v_type_4149_ = lean_ctor_get(v_toConstantVal_4145_, 2);
lean_inc_ref(v_type_4149_);
lean_dec_ref(v_toConstantVal_4145_);
v___x_4150_ = l_Lean_Meta_isPropFormerType(v_type_4149_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; uint8_t v___x_4152_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4152_ = lean_unbox(v_a_4151_);
lean_dec(v_a_4151_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_inc_n(v_indName_3966_, 2);
v___x_4153_ = l_Lean_mkRecName(v_indName_3966_);
v___x_4154_ = l_Lean_mkBRecOnName(v_indName_3966_);
lean_inc(v_all_4147_);
v___x_4155_ = lean_array_mk(v_all_4147_);
lean_inc(v___x_4154_);
lean_inc_ref(v___x_4155_);
lean_inc(v_numParams_4146_);
lean_inc(v___x_4153_);
v___x_4156_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4153_, v_numParams_4146_, v___x_4155_, v___x_4154_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; 
lean_dec_ref_known(v___x_4156_, 1);
v___x_4157_ = lean_unsigned_to_nat(0u);
v___x_4158_ = l_List_get_x21Internal___redArg(v___x_3976_, v_all_4147_, v___x_4157_);
lean_dec(v_all_4147_);
v___x_4159_ = lean_name_eq(v___x_4158_, v_indName_3966_);
lean_dec(v_indName_3966_);
lean_dec(v___x_4158_);
if (v___x_4159_ == 0)
{
lean_object* v___x_4160_; 
lean_dec_ref(v___x_4155_);
lean_dec(v___x_4154_);
lean_dec(v___x_4153_);
lean_dec(v_numNested_4148_);
lean_dec(v_numParams_4146_);
v___x_4160_ = lean_box(0);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v___x_4160_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = lean_box(0);
v___x_4162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4148_, v___x_4153_, v___x_4154_, v_numParams_4146_, v___x_4155_, v___x_4157_, v___x_4161_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
lean_dec(v_numNested_4148_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_dec_ref_known(v___x_4162_, 1);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v___x_4161_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___y_4099_ = v_a_4105_;
v___y_4100_ = v___x_4139_;
v_a_4101_ = v_a_4163_;
goto v___jp_4098_;
}
}
}
else
{
lean_dec_ref(v___x_4155_);
lean_dec(v___x_4154_);
lean_dec(v___x_4153_);
lean_dec(v_numNested_4148_);
lean_dec(v_all_4147_);
lean_dec(v_numParams_4146_);
lean_dec(v_indName_3966_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4156_, 1);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v_a_4164_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4165_; 
v_a_4165_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4156_, 1);
v___y_4099_ = v_a_4105_;
v___y_4100_ = v___x_4139_;
v_a_4101_ = v_a_4165_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v___x_4166_; 
lean_dec(v_numNested_4148_);
lean_dec(v_all_4147_);
lean_dec(v_numParams_4146_);
lean_dec(v_indName_3966_);
v___x_4166_ = lean_box(0);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v___x_4166_;
goto v___jp_4093_;
}
}
else
{
lean_object* v_a_4167_; 
lean_dec(v_numNested_4148_);
lean_dec(v_all_4147_);
lean_dec(v_numParams_4146_);
lean_dec(v_indName_3966_);
v_a_4167_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4150_, 1);
v___y_4099_ = v_a_4105_;
v___y_4100_ = v___x_4139_;
v_a_4101_ = v_a_4167_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v___x_4168_; 
lean_dec(v_a_4141_);
lean_dec(v_indName_3966_);
v___x_4168_ = lean_box(0);
v___y_4094_ = v_a_4105_;
v___y_4095_ = v___x_4139_;
v_a_4096_ = v___x_4168_;
goto v___jp_4093_;
}
}
else
{
lean_object* v_a_4169_; 
lean_dec(v_indName_3966_);
v_a_4169_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4099_ = v_a_4105_;
v___y_4100_ = v___x_4139_;
v_a_4101_ = v_a_4169_;
goto v___jp_4098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_mkBRecOn(v_indName_4246_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4253_, lean_object* v___x_4254_, lean_object* v___x_4255_, lean_object* v___x_4256_, lean_object* v___x_4257_, lean_object* v_inst_4258_, lean_object* v_R_4259_, lean_object* v_a_4260_, lean_object* v_b_4261_, lean_object* v_c_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; 
v___x_4268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4253_, v___x_4254_, v___x_4255_, v___x_4256_, v___x_4257_, v_a_4260_, v_b_4261_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4269_, lean_object* v___x_4270_, lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v___x_4273_, lean_object* v_inst_4274_, lean_object* v_R_4275_, lean_object* v_a_4276_, lean_object* v_b_4277_, lean_object* v_c_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4269_, v___x_4270_, v___x_4271_, v___x_4272_, v___x_4273_, v_inst_4274_, v_R_4275_, v_a_4276_, v_b_4277_, v_c_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v_upperBound_4269_);
return v_res_4284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = lean_unsigned_to_nat(2304625798u);
v___x_4331_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4332_ = l_Lean_Name_num___override(v___x_4331_, v___x_4330_);
return v___x_4332_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4335_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4336_ = l_Lean_Name_str___override(v___x_4335_, v___x_4334_);
return v___x_4336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4339_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4340_ = l_Lean_Name_str___override(v___x_4339_, v___x_4338_);
return v___x_4340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_unsigned_to_nat(2u);
v___x_4342_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4343_ = l_Lean_Name_num___override(v___x_4342_, v___x_4341_);
return v___x_4343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4345_; uint8_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4345_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4346_ = 0;
v___x_4347_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4348_ = l_Lean_registerTraceClass(v___x_4345_, v___x_4346_, v___x_4347_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4350_;
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
