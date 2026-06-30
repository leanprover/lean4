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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19;
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "below_"};
static const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "F_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_2104__boxed_100_; lean_object* v_res_101_; 
v___x_2104__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_2104__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
uint8_t v___x_2259__boxed_251_; uint8_t v___x_2260__boxed_252_; lean_object* v_res_253_; 
v___x_2259__boxed_251_ = lean_unbox(v___x_239_);
v___x_2260__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2259__boxed_251_, v___x_2260__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
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
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Lean_Expr_fvarId_x21(v_head_258_);
lean_dec_ref(v_head_258_);
v___x_278_ = l_Lean_FVarId_getUserName___redArg(v___x_277_, v___y_262_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v___f_281_; uint8_t v___x_282_; lean_object* v___x_283_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = lean_box(v___x_269_);
lean_inc(v_rlvl_255_);
v___f_281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_281_, 0, v_rlvl_255_);
lean_closure_set(v___f_281_, 1, v___x_280_);
v___x_282_ = 0;
v___x_283_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_259_, v___f_281_, v___x_282_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref_known(v___x_283_, 1);
v___x_285_ = lean_box(v___x_282_);
v___x_286_ = lean_box(v___x_269_);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1___boxed), 14, 8);
lean_closure_set(v___f_287_, 0, v_arg__args_260_);
lean_closure_set(v___f_287_, 1, v_arg__type_261_);
lean_closure_set(v___f_287_, 2, v___x_285_);
lean_closure_set(v___f_287_, 3, v___x_286_);
lean_closure_set(v___f_287_, 4, v_prods_256_);
lean_closure_set(v___f_287_, 5, v_rlvl_255_);
lean_closure_set(v___f_287_, 6, v_motives_254_);
lean_closure_set(v___f_287_, 7, v_tail_257_);
v___x_288_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_279_, v_a_284_, v___f_287_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
return v___x_288_;
}
else
{
lean_dec(v_a_279_);
lean_dec_ref(v_arg__type_261_);
lean_dec_ref(v_arg__args_260_);
lean_dec(v_tail_257_);
lean_dec_ref(v_prods_256_);
lean_dec(v_rlvl_255_);
lean_dec_ref(v_motives_254_);
return v___x_283_;
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_arg__type_261_);
lean_dec_ref(v_arg__args_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_tail_257_);
lean_dec_ref(v_prods_256_);
lean_dec(v_rlvl_255_);
lean_dec_ref(v_motives_254_);
v_a_289_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_278_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_278_);
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
lean_object* v___f_435_; lean_object* v___x_4964__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_4964__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_4964__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
uint8_t v___x_9166__boxed_555_; lean_object* v_res_556_; 
v___x_9166__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9166__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_x_549_);
lean_dec_ref(v_targs_548_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(lean_object* v___x_557_, lean_object* v_as_558_, size_t v_sz_559_, size_t v_i_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
uint8_t v___x_567_; 
v___x_567_ = lean_usize_dec_lt(v_i_560_, v_sz_559_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; 
lean_dec(v___x_557_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v_b_561_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_array_uget_borrowed(v_as_558_, v_i_560_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
lean_inc(v_a_569_);
v___x_570_ = lean_infer_type(v_a_569_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___f_573_; uint8_t v___x_574_; lean_object* v___x_575_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = lean_box(v___x_567_);
lean_inc(v___x_557_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_573_, 0, v___x_557_);
lean_closure_set(v___f_573_, 1, v___x_572_);
v___x_574_ = 0;
v___x_575_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_571_, v___f_573_, v___x_574_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_575_, 1);
v___x_577_ = l_Lean_Expr_app___override(v_b_561_, v_a_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_560_, v___x_578_);
v_i_560_ = v___x_579_;
v_b_561_ = v___x_577_;
goto _start;
}
else
{
lean_dec_ref(v_b_561_);
lean_dec(v___x_557_);
return v___x_575_;
}
}
else
{
lean_dec_ref(v_b_561_);
lean_dec(v___x_557_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___boxed(lean_object* v___x_581_, lean_object* v_as_582_, lean_object* v_sz_583_, lean_object* v_i_584_, lean_object* v_b_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
size_t v_sz_boxed_591_; size_t v_i_boxed_592_; lean_object* v_res_593_; 
v_sz_boxed_591_ = lean_unbox_usize(v_sz_583_);
lean_dec(v_sz_583_);
v_i_boxed_592_ = lean_unbox_usize(v_i_584_);
lean_dec(v_i_584_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_581_, v_as_582_, v_sz_boxed_591_, v_i_boxed_592_, v_b_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec_ref(v_as_582_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(lean_object* v_msgData_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; lean_object* v_env_601_; lean_object* v___x_602_; lean_object* v_mctx_603_; lean_object* v_lctx_604_; lean_object* v_options_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_600_ = lean_st_ref_get(v___y_598_);
v_env_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc_ref(v_env_601_);
lean_dec(v___x_600_);
v___x_602_ = lean_st_ref_get(v___y_596_);
v_mctx_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_mctx_603_);
lean_dec(v___x_602_);
v_lctx_604_ = lean_ctor_get(v___y_595_, 2);
v_options_605_ = lean_ctor_get(v___y_597_, 2);
lean_inc_ref(v_options_605_);
lean_inc_ref(v_lctx_604_);
v___x_606_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_606_, 0, v_env_601_);
lean_ctor_set(v___x_606_, 1, v_mctx_603_);
lean_ctor_set(v___x_606_, 2, v_lctx_604_);
lean_ctor_set(v___x_606_, 3, v_options_605_);
v___x_607_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v_msgData_594_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_ref_622_; lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_632_; 
v_ref_622_ = lean_ctor_get(v___y_619_, 5);
v___x_623_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_632_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_632_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_630_; 
lean_inc(v_ref_622_);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_ref_622_);
lean_ctor_set(v___x_628_, 1, v_a_624_);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_630_ = v___x_626_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_644_ = lean_unsigned_to_nat(4u);
v___x_645_ = lean_unsigned_to_nat(68u);
v___x_646_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_648_ = l_mkPanicMessageWithDecl(v___x_647_, v___x_646_, v___x_645_, v___x_644_, v___x_643_);
return v___x_648_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_655_, lean_object* v_numMotives_656_, lean_object* v_numMinors_657_, lean_object* v_head_658_, lean_object* v_tail_659_, lean_object* v_recName_660_, lean_object* v_belowName_661_, lean_object* v_levelParams_662_, lean_object* v_refArgs_663_, lean_object* v_x_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_670_ = lean_nat_add(v_nParams_655_, v_numMotives_656_);
v___x_671_ = lean_nat_add(v___x_670_, v_numMinors_657_);
v___x_672_ = lean_array_get_size(v_refArgs_663_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; 
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
lean_dec(v_recName_660_);
lean_dec(v_tail_659_);
lean_dec(v_head_658_);
lean_dec(v_nParams_655_);
v___x_674_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_675_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_674_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_676_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_655_);
lean_inc_ref(v_refArgs_663_);
v___x_677_ = l_Array_toSubarray___redArg(v_refArgs_663_, v___x_676_, v_nParams_655_);
v___x_678_ = lean_unsigned_to_nat(1u);
v___x_679_ = lean_nat_sub(v___x_672_, v___x_678_);
v___x_680_ = l_Lean_instInhabitedExpr;
v___x_681_ = lean_array_get(v___x_680_, v_refArgs_663_, v___x_679_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___x_681_);
v___x_682_ = lean_infer_type(v___x_681_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref_known(v___x_682_, 1);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
v___x_684_ = lean_infer_type(v_a_683_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = l_Lean_Meta_typeFormerTypeLevel(v_a_685_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
if (lean_obj_tag(v_a_687_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; 
v_val_688_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_a_687_, 1);
lean_inc(v___x_670_);
lean_inc_ref(v_refArgs_663_);
v___x_689_ = l_Array_toSubarray___redArg(v_refArgs_663_, v_nParams_655_, v___x_670_);
v___x_690_ = l_Subarray_copy___redArg(v___x_677_);
v___x_691_ = l_Subarray_copy___redArg(v___x_689_);
v___x_692_ = l_Lean_mkLevelMax(v_val_688_, v_head_658_);
lean_inc_n(v___x_692_, 2);
v___x_693_ = l_Lean_Level_succ___override(v___x_692_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_tail_659_);
v___x_695_ = l_Lean_Expr_const___override(v_recName_660_, v___x_694_);
v___x_696_ = l_Lean_mkAppN(v___x_695_, v___x_690_);
v_sz_697_ = lean_array_size(v___x_691_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_692_, v___x_691_, v_sz_697_, v___x_698_, v___x_696_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; size_t v_sz_703_; lean_object* v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
lean_inc(v___x_671_);
lean_inc_ref(v_refArgs_663_);
v___x_701_ = l_Array_toSubarray___redArg(v_refArgs_663_, v___x_670_, v___x_671_);
v___x_702_ = l_Subarray_copy___redArg(v___x_701_);
v_sz_703_ = lean_array_size(v___x_702_);
lean_inc_ref(v___x_691_);
lean_inc(v___x_692_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_692_, v___x_691_, v___x_702_, v_sz_703_, v___x_698_, v_a_700_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec_ref(v___x_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = l_Array_toSubarray___redArg(v_refArgs_663_, v___x_671_, v___x_679_);
v___x_707_ = l_Subarray_copy___redArg(v___x_706_);
v___x_708_ = l_Lean_mkAppN(v_a_705_, v___x_707_);
lean_inc(v___x_681_);
v___x_709_ = l_Lean_Expr_app___override(v___x_708_, v___x_681_);
v___x_710_ = l_Array_append___redArg(v___x_690_, v___x_691_);
lean_dec_ref(v___x_691_);
v___x_711_ = l_Array_append___redArg(v___x_710_, v___x_707_);
lean_dec_ref(v___x_707_);
v___x_712_ = lean_mk_empty_array_with_capacity(v___x_678_);
v___x_713_ = lean_array_push(v___x_712_, v___x_681_);
v___x_714_ = l_Array_append___redArg(v___x_711_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_715_ = l_Lean_Expr_sort___override(v___x_692_);
v___x_716_ = 0;
v___x_717_ = 1;
v___x_718_ = l_Lean_Meta_mkForallFVars(v___x_714_, v___x_715_, v___x_716_, v___x_673_, v___x_673_, v___x_717_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_Meta_mkLambdaFVars(v___x_714_, v___x_709_, v___x_716_, v___x_673_, v___x_716_, v___x_673_, v___x_717_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec_ref(v___x_714_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v___x_722_ = lean_box(1);
v___x_723_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_661_, v_levelParams_662_, v_a_719_, v_a_721_, v___x_722_, v___y_668_);
return v___x_723_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_719_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
v_a_724_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_720_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_720_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_709_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
v_a_732_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_718_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_718_);
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
lean_dec(v___x_692_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_690_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_671_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
v_a_740_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_704_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_704_);
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
lean_dec(v___x_692_);
lean_dec_ref(v___x_691_);
lean_dec_ref(v___x_690_);
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
v_a_748_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_699_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_699_);
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
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec(v_a_687_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
lean_dec(v_recName_660_);
lean_dec(v_tail_659_);
lean_dec(v_head_658_);
lean_dec(v_nParams_655_);
v___x_756_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_757_ = l_Lean_MessageData_ofExpr(v___x_681_);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_760_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_761_;
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
lean_dec(v_recName_660_);
lean_dec(v_tail_659_);
lean_dec(v_head_658_);
lean_dec(v_nParams_655_);
v_a_762_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_686_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_686_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
lean_dec(v_recName_660_);
lean_dec(v_tail_659_);
lean_dec(v_head_658_);
lean_dec(v_nParams_655_);
v_a_770_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_684_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_684_);
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
lean_dec(v___x_681_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_677_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec_ref(v_refArgs_663_);
lean_dec(v_levelParams_662_);
lean_dec(v_belowName_661_);
lean_dec(v_recName_660_);
lean_dec(v_tail_659_);
lean_dec(v_head_658_);
lean_dec(v_nParams_655_);
v_a_778_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_682_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_682_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_786_, lean_object* v_numMotives_787_, lean_object* v_numMinors_788_, lean_object* v_head_789_, lean_object* v_tail_790_, lean_object* v_recName_791_, lean_object* v_belowName_792_, lean_object* v_levelParams_793_, lean_object* v_refArgs_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_786_, v_numMotives_787_, v_numMinors_788_, v_head_789_, v_tail_790_, v_recName_791_, v_belowName_792_, v_levelParams_793_, v_refArgs_794_, v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec_ref(v_x_795_);
lean_dec(v_numMinors_788_);
lean_dec(v_numMotives_787_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
if (lean_obj_tag(v_a_802_) == 0)
{
lean_object* v___x_804_; 
v___x_804_ = l_List_reverse___redArg(v_a_803_);
return v___x_804_;
}
else
{
lean_object* v_head_805_; lean_object* v_tail_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_815_; 
v_head_805_ = lean_ctor_get(v_a_802_, 0);
v_tail_806_ = lean_ctor_get(v_a_802_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_802_);
if (v_isSharedCheck_815_ == 0)
{
v___x_808_ = v_a_802_;
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_tail_806_);
lean_inc(v_head_805_);
lean_dec(v_a_802_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_815_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Lean_Level_param___override(v_head_805_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_a_803_);
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_a_803_);
v___x_812_ = v_reuseFailAlloc_814_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
v_a_802_ = v_tail_806_;
v_a_803_ = v___x_812_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_816_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_822_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
lean_ctor_set(v___x_822_, 3, v___x_821_);
lean_ctor_set(v___x_822_, 4, v___x_821_);
lean_ctor_set(v___x_822_, 5, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_823_, uint8_t v_s_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_env_829_; lean_object* v_nextMacroScope_830_; lean_object* v_ngen_831_; lean_object* v_auxDeclNGen_832_; lean_object* v_traceState_833_; lean_object* v_messages_834_; lean_object* v_infoState_835_; lean_object* v_snapshotTasks_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_865_; 
v___x_828_ = lean_st_ref_take(v___y_826_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
v_nextMacroScope_830_ = lean_ctor_get(v___x_828_, 1);
v_ngen_831_ = lean_ctor_get(v___x_828_, 2);
v_auxDeclNGen_832_ = lean_ctor_get(v___x_828_, 3);
v_traceState_833_ = lean_ctor_get(v___x_828_, 4);
v_messages_834_ = lean_ctor_get(v___x_828_, 6);
v_infoState_835_ = lean_ctor_get(v___x_828_, 7);
v_snapshotTasks_836_ = lean_ctor_get(v___x_828_, 8);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_865_ == 0)
{
lean_object* v_unused_866_; 
v_unused_866_ = lean_ctor_get(v___x_828_, 5);
lean_dec(v_unused_866_);
v___x_838_ = v___x_828_;
v_isShared_839_ = v_isSharedCheck_865_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snapshotTasks_836_);
lean_inc(v_infoState_835_);
lean_inc(v_messages_834_);
lean_inc(v_traceState_833_);
lean_inc(v_auxDeclNGen_832_);
lean_inc(v_ngen_831_);
lean_inc(v_nextMacroScope_830_);
lean_inc(v_env_829_);
lean_dec(v___x_828_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_865_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_840_ = 0;
v___x_841_ = lean_box(0);
v___x_842_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_829_, v_declName_823_, v_s_824_, v___x_840_, v___x_841_);
v___x_843_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 5, v___x_843_);
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_nextMacroScope_830_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_ngen_831_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_auxDeclNGen_832_);
lean_ctor_set(v_reuseFailAlloc_864_, 4, v_traceState_833_);
lean_ctor_set(v_reuseFailAlloc_864_, 5, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_864_, 6, v_messages_834_);
lean_ctor_set(v_reuseFailAlloc_864_, 7, v_infoState_835_);
lean_ctor_set(v_reuseFailAlloc_864_, 8, v_snapshotTasks_836_);
v___x_845_ = v_reuseFailAlloc_864_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_mctx_848_; lean_object* v_zetaDeltaFVarIds_849_; lean_object* v_postponed_850_; lean_object* v_diag_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_862_; 
v___x_846_ = lean_st_ref_set(v___y_826_, v___x_845_);
v___x_847_ = lean_st_ref_take(v___y_825_);
v_mctx_848_ = lean_ctor_get(v___x_847_, 0);
v_zetaDeltaFVarIds_849_ = lean_ctor_get(v___x_847_, 2);
v_postponed_850_ = lean_ctor_get(v___x_847_, 3);
v_diag_851_ = lean_ctor_get(v___x_847_, 4);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v___x_847_, 1);
lean_dec(v_unused_863_);
v___x_853_ = v___x_847_;
v_isShared_854_ = v_isSharedCheck_862_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_diag_851_);
lean_inc(v_postponed_850_);
lean_inc(v_zetaDeltaFVarIds_849_);
lean_inc(v_mctx_848_);
lean_dec(v___x_847_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_862_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_mctx_848_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_zetaDeltaFVarIds_849_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_postponed_850_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v_diag_851_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_st_ref_set(v___y_825_, v___x_857_);
v___x_859_ = lean_box(0);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_867_, lean_object* v_s_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v_s_boxed_872_; lean_object* v_res_873_; 
v_s_boxed_872_ = lean_unbox(v_s_868_);
v_res_873_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_867_, v_s_boxed_872_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_880_; lean_object* v___x_881_; 
v___x_880_ = 0;
v___x_881_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_874_, v___x_880_, v___y_876_, v___y_878_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_fileName_896_; lean_object* v_fileMap_897_; lean_object* v_options_898_; lean_object* v_currRecDepth_899_; lean_object* v_maxRecDepth_900_; lean_object* v_ref_901_; lean_object* v_currNamespace_902_; lean_object* v_openDecls_903_; lean_object* v_initHeartbeats_904_; lean_object* v_maxHeartbeats_905_; lean_object* v_quotContext_906_; lean_object* v_currMacroScope_907_; uint8_t v_diag_908_; lean_object* v_cancelTk_x3f_909_; uint8_t v_suppressElabErrors_910_; lean_object* v_inheritedTraceOptions_911_; lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_fileName_896_ = lean_ctor_get(v___y_893_, 0);
v_fileMap_897_ = lean_ctor_get(v___y_893_, 1);
v_options_898_ = lean_ctor_get(v___y_893_, 2);
v_currRecDepth_899_ = lean_ctor_get(v___y_893_, 3);
v_maxRecDepth_900_ = lean_ctor_get(v___y_893_, 4);
v_ref_901_ = lean_ctor_get(v___y_893_, 5);
v_currNamespace_902_ = lean_ctor_get(v___y_893_, 6);
v_openDecls_903_ = lean_ctor_get(v___y_893_, 7);
v_initHeartbeats_904_ = lean_ctor_get(v___y_893_, 8);
v_maxHeartbeats_905_ = lean_ctor_get(v___y_893_, 9);
v_quotContext_906_ = lean_ctor_get(v___y_893_, 10);
v_currMacroScope_907_ = lean_ctor_get(v___y_893_, 11);
v_diag_908_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*14);
v_cancelTk_x3f_909_ = lean_ctor_get(v___y_893_, 12);
v_suppressElabErrors_910_ = lean_ctor_get_uint8(v___y_893_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_911_ = lean_ctor_get(v___y_893_, 13);
v_ref_912_ = l_Lean_replaceRef(v_ref_889_, v_ref_901_);
lean_inc_ref(v_inheritedTraceOptions_911_);
lean_inc(v_cancelTk_x3f_909_);
lean_inc(v_currMacroScope_907_);
lean_inc(v_quotContext_906_);
lean_inc(v_maxHeartbeats_905_);
lean_inc(v_initHeartbeats_904_);
lean_inc(v_openDecls_903_);
lean_inc(v_currNamespace_902_);
lean_inc(v_maxRecDepth_900_);
lean_inc(v_currRecDepth_899_);
lean_inc_ref(v_options_898_);
lean_inc_ref(v_fileMap_897_);
lean_inc_ref(v_fileName_896_);
v___x_913_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_913_, 0, v_fileName_896_);
lean_ctor_set(v___x_913_, 1, v_fileMap_897_);
lean_ctor_set(v___x_913_, 2, v_options_898_);
lean_ctor_set(v___x_913_, 3, v_currRecDepth_899_);
lean_ctor_set(v___x_913_, 4, v_maxRecDepth_900_);
lean_ctor_set(v___x_913_, 5, v_ref_912_);
lean_ctor_set(v___x_913_, 6, v_currNamespace_902_);
lean_ctor_set(v___x_913_, 7, v_openDecls_903_);
lean_ctor_set(v___x_913_, 8, v_initHeartbeats_904_);
lean_ctor_set(v___x_913_, 9, v_maxHeartbeats_905_);
lean_ctor_set(v___x_913_, 10, v_quotContext_906_);
lean_ctor_set(v___x_913_, 11, v_currMacroScope_907_);
lean_ctor_set(v___x_913_, 12, v_cancelTk_x3f_909_);
lean_ctor_set(v___x_913_, 13, v_inheritedTraceOptions_911_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*14, v_diag_908_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*14 + 1, v_suppressElabErrors_910_);
v___x_914_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_890_, v___y_891_, v___y_892_, v___x_913_, v___y_894_);
lean_dec_ref_known(v___x_913_, 14);
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
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_923_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_932_ = ((size_t)5ULL);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_unsigned_to_nat(32u);
v___x_935_ = lean_mk_empty_array_with_capacity(v___x_934_);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_937_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
lean_ctor_set(v___x_937_, 2, v___x_933_);
lean_ctor_set(v___x_937_, 3, v___x_933_);
lean_ctor_set_usize(v___x_937_, 4, v___x_932_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = lean_box(1);
v___x_939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_938_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_963_, lean_object* v_declHint_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; lean_object* v_env_968_; uint8_t v___x_969_; 
v___x_967_ = lean_st_ref_get(v___y_965_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_969_ = l_Lean_Name_isAnonymous(v_declHint_964_);
if (v___x_969_ == 0)
{
uint8_t v_isExporting_970_; 
v_isExporting_970_ = lean_ctor_get_uint8(v_env_968_, sizeof(void*)*8);
if (v_isExporting_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_964_);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v_msg_963_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
lean_inc_ref(v_env_968_);
v___x_972_ = l_Lean_Environment_setExporting(v_env_968_, v___x_969_);
lean_inc(v_declHint_964_);
lean_inc_ref(v___x_972_);
v___x_973_ = l_Lean_Environment_contains(v___x_972_, v_declHint_964_, v_isExporting_970_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_964_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v_msg_963_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_c_980_; lean_object* v___x_981_; 
v___x_975_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_977_ = l_Lean_Options_empty;
v___x_978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_978_, 0, v___x_972_);
lean_ctor_set(v___x_978_, 1, v___x_975_);
lean_ctor_set(v___x_978_, 2, v___x_976_);
lean_ctor_set(v___x_978_, 3, v___x_977_);
lean_inc(v_declHint_964_);
v___x_979_ = l_Lean_MessageData_ofConstName(v_declHint_964_, v___x_969_);
v_c_980_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_980_, 0, v___x_978_);
lean_ctor_set(v_c_980_, 1, v___x_979_);
v___x_981_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_968_, v_declHint_964_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_964_);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v_c_980_);
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = l_Lean_MessageData_note(v___x_985_);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v_msg_963_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_val_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1024_; 
v_val_989_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_991_ = v___x_981_;
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_val_989_);
lean_dec(v___x_981_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1024_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_mod_996_; uint8_t v___x_997_; 
v___x_993_ = lean_box(0);
v___x_994_ = l_Lean_Environment_header(v_env_968_);
lean_dec_ref(v_env_968_);
v___x_995_ = l_Lean_EnvironmentHeader_moduleNames(v___x_994_);
v_mod_996_ = lean_array_get(v___x_993_, v___x_995_, v_val_989_);
lean_dec(v_val_989_);
lean_dec_ref(v___x_995_);
v___x_997_ = l_Lean_isPrivateName(v_declHint_964_);
lean_dec(v_declHint_964_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_998_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v_c_980_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_MessageData_ofName(v_mod_996_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_MessageData_note(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v_msg_963_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 0);
lean_ctor_set(v___x_991_, 0, v___x_1007_);
v___x_1009_ = v___x_991_;
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
v___x_1011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_c_980_);
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_MessageData_ofName(v_mod_996_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Lean_MessageData_note(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_963_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
if (v_isShared_992_ == 0)
{
lean_ctor_set_tag(v___x_991_, 0);
lean_ctor_set(v___x_991_, 0, v___x_1020_);
v___x_1022_ = v___x_991_;
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
lean_dec_ref(v_env_968_);
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
v_ref_1111_ = lean_ctor_get(v___y_1108_, 5);
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
lean_object* v___x_1163_; 
lean_inc(v_recName_1155_);
v___x_1163_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1155_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___x_1163_, 1);
if (lean_obj_tag(v_a_1164_) == 7)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1280_; 
v_val_1165_ = lean_ctor_get(v_a_1164_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1167_ = v_a_1164_;
v_isShared_1168_ = v_isSharedCheck_1280_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v_a_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1280_;
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
v___f_1178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1178_, 0, v_nParams_1156_);
lean_closure_set(v___f_1178_, 1, v_numMotives_1170_);
lean_closure_set(v___f_1178_, 2, v_numMinors_1171_);
lean_closure_set(v___f_1178_, 3, v_head_1176_);
lean_closure_set(v___f_1178_, 4, v_tail_1177_);
lean_closure_set(v___f_1178_, 5, v_recName_1155_);
lean_closure_set(v___f_1178_, 6, v_belowName_1157_);
lean_closure_set(v___f_1178_, 7, v_levelParams_1172_);
v___x_1179_ = 0;
v___x_1180_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1173_, v___f_1178_, v___x_1179_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
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
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1181_);
v___x_1183_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_addDecl(v___x_1183_, v___x_1179_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_toConstantVal_1185_; lean_object* v_name_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref_known(v___x_1184_, 1);
v_toConstantVal_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_toConstantVal_1185_);
lean_dec(v_a_1181_);
v_name_1186_ = lean_ctor_get(v_toConstantVal_1185_, 0);
lean_inc_n(v_name_1186_, 2);
lean_dec_ref(v_toConstantVal_1185_);
v___x_1187_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1186_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1187_, 0);
lean_dec(v_unused_1264_);
v___x_1189_ = v___x_1187_;
v_isShared_1190_ = v_isSharedCheck_1263_;
goto v_resetjp_1188_;
}
else
{
lean_dec(v___x_1187_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1263_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_env_1192_; lean_object* v_nextMacroScope_1193_; lean_object* v_ngen_1194_; lean_object* v_auxDeclNGen_1195_; lean_object* v_traceState_1196_; lean_object* v_messages_1197_; lean_object* v_infoState_1198_; lean_object* v_snapshotTasks_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1261_; 
v___x_1191_ = lean_st_ref_take(v_a_1161_);
v_env_1192_ = lean_ctor_get(v___x_1191_, 0);
v_nextMacroScope_1193_ = lean_ctor_get(v___x_1191_, 1);
v_ngen_1194_ = lean_ctor_get(v___x_1191_, 2);
v_auxDeclNGen_1195_ = lean_ctor_get(v___x_1191_, 3);
v_traceState_1196_ = lean_ctor_get(v___x_1191_, 4);
v_messages_1197_ = lean_ctor_get(v___x_1191_, 6);
v_infoState_1198_ = lean_ctor_get(v___x_1191_, 7);
v_snapshotTasks_1199_ = lean_ctor_get(v___x_1191_, 8);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1191_, 5);
lean_dec(v_unused_1262_);
v___x_1201_ = v___x_1191_;
v_isShared_1202_ = v_isSharedCheck_1261_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snapshotTasks_1199_);
lean_inc(v_infoState_1198_);
lean_inc(v_messages_1197_);
lean_inc(v_traceState_1196_);
lean_inc(v_auxDeclNGen_1195_);
lean_inc(v_ngen_1194_);
lean_inc(v_nextMacroScope_1193_);
lean_inc(v_env_1192_);
lean_dec(v___x_1191_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1261_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_inc(v_name_1186_);
v___x_1203_ = l_Lean_markAuxRecursor(v_env_1192_, v_name_1186_);
v___x_1204_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 5, v___x_1204_);
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_nextMacroScope_1193_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_ngen_1194_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_auxDeclNGen_1195_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_traceState_1196_);
lean_ctor_set(v_reuseFailAlloc_1260_, 5, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1260_, 6, v_messages_1197_);
lean_ctor_set(v_reuseFailAlloc_1260_, 7, v_infoState_1198_);
lean_ctor_set(v_reuseFailAlloc_1260_, 8, v_snapshotTasks_1199_);
v___x_1206_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v_mctx_1209_; lean_object* v_zetaDeltaFVarIds_1210_; lean_object* v_postponed_1211_; lean_object* v_diag_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1258_; 
v___x_1207_ = lean_st_ref_set(v_a_1161_, v___x_1206_);
v___x_1208_ = lean_st_ref_take(v_a_1159_);
v_mctx_1209_ = lean_ctor_get(v___x_1208_, 0);
v_zetaDeltaFVarIds_1210_ = lean_ctor_get(v___x_1208_, 2);
v_postponed_1211_ = lean_ctor_get(v___x_1208_, 3);
v_diag_1212_ = lean_ctor_get(v___x_1208_, 4);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1259_);
v___x_1214_ = v___x_1208_;
v_isShared_1215_ = v_isSharedCheck_1258_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_diag_1212_);
lean_inc(v_postponed_1211_);
lean_inc(v_zetaDeltaFVarIds_1210_);
lean_inc(v_mctx_1209_);
lean_dec(v___x_1208_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1258_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_mctx_1209_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_zetaDeltaFVarIds_1210_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_postponed_1211_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_diag_1212_);
v___x_1218_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_env_1221_; lean_object* v_nextMacroScope_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_messages_1226_; lean_object* v_infoState_1227_; lean_object* v_snapshotTasks_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1255_; 
v___x_1219_ = lean_st_ref_set(v_a_1159_, v___x_1218_);
v___x_1220_ = lean_st_ref_take(v_a_1161_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
v_nextMacroScope_1222_ = lean_ctor_get(v___x_1220_, 1);
v_ngen_1223_ = lean_ctor_get(v___x_1220_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1220_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1220_, 4);
v_messages_1226_ = lean_ctor_get(v___x_1220_, 6);
v_infoState_1227_ = lean_ctor_get(v___x_1220_, 7);
v_snapshotTasks_1228_ = lean_ctor_get(v___x_1220_, 8);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1220_, 5);
lean_dec(v_unused_1256_);
v___x_1230_ = v___x_1220_;
v_isShared_1231_ = v_isSharedCheck_1255_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snapshotTasks_1228_);
lean_inc(v_infoState_1227_);
lean_inc(v_messages_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_nextMacroScope_1222_);
lean_inc(v_env_1221_);
lean_dec(v___x_1220_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1255_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = l_Lean_addProtected(v_env_1221_, v_name_1186_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 5, v___x_1204_);
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_nextMacroScope_1222_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1254_, 5, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1254_, 6, v_messages_1226_);
lean_ctor_set(v_reuseFailAlloc_1254_, 7, v_infoState_1227_);
lean_ctor_set(v_reuseFailAlloc_1254_, 8, v_snapshotTasks_1228_);
v___x_1234_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_mctx_1237_; lean_object* v_zetaDeltaFVarIds_1238_; lean_object* v_postponed_1239_; lean_object* v_diag_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1252_; 
v___x_1235_ = lean_st_ref_set(v_a_1161_, v___x_1234_);
v___x_1236_ = lean_st_ref_take(v_a_1159_);
v_mctx_1237_ = lean_ctor_get(v___x_1236_, 0);
v_zetaDeltaFVarIds_1238_ = lean_ctor_get(v___x_1236_, 2);
v_postponed_1239_ = lean_ctor_get(v___x_1236_, 3);
v_diag_1240_ = lean_ctor_get(v___x_1236_, 4);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1236_, 1);
lean_dec(v_unused_1253_);
v___x_1242_ = v___x_1236_;
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_diag_1240_);
lean_inc(v_postponed_1239_);
lean_inc(v_zetaDeltaFVarIds_1238_);
lean_inc(v_mctx_1237_);
lean_dec(v___x_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1252_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1216_);
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_mctx_1237_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_zetaDeltaFVarIds_1238_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_postponed_1239_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_diag_1240_);
v___x_1245_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1246_ = lean_st_ref_set(v_a_1159_, v___x_1245_);
v___x_1247_ = lean_box(0);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1247_);
v___x_1249_ = v___x_1189_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
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
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_del_object(v___x_1167_);
v_a_1266_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1180_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1180_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec(v___x_1175_);
lean_dec_ref(v_type_1173_);
lean_dec(v_levelParams_1172_);
lean_dec(v_numMinors_1171_);
lean_dec(v_numMotives_1170_);
lean_del_object(v___x_1167_);
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1275_ = l_Lean_MessageData_ofName(v_recName_1155_);
v___x_1276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1274_);
lean_ctor_set(v___x_1276_, 1, v___x_1275_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1276_);
lean_ctor_set(v___x_1278_, 1, v___x_1277_);
v___x_1279_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1278_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1279_;
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
lean_dec(v_a_1164_);
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
v___x_1281_ = l_Lean_MessageData_ofName(v_recName_1155_);
v___x_1282_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1283_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
return v___x_1284_;
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_belowName_1157_);
lean_dec(v_nParams_1156_);
lean_dec(v_recName_1155_);
v_a_1285_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1163_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1163_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1293_, lean_object* v_nParams_1294_, lean_object* v_belowName_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1293_, v_nParams_1294_, v_belowName_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1302_, lean_object* v_msg_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1310_, lean_object* v_msg_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1310_, v_msg_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1318_, uint8_t v_s_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1318_, v_s_1319_, v___y_1321_, v___y_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1326_, lean_object* v_s_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v_s_boxed_1333_; lean_object* v_res_1334_; 
v_s_boxed_1333_ = lean_unbox(v_s_1327_);
v_res_1334_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1326_, v_s_boxed_1333_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1335_, lean_object* v_constName_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_constName_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1343_, v_constName_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1351_, lean_object* v_ref_1352_, lean_object* v_constName_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1352_, v_constName_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_ref_1361_, lean_object* v_constName_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1360_, v_ref_1361_, v_constName_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v_ref_1361_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1369_, lean_object* v_ref_1370_, lean_object* v_msg_1371_, lean_object* v_declHint_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1370_, v_msg_1371_, v_declHint_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_ref_1380_, lean_object* v_msg_1381_, lean_object* v_declHint_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1379_, v_ref_1380_, v_msg_1381_, v_declHint_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v_ref_1380_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1389_, lean_object* v_declHint_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1389_, v_declHint_1390_, v___y_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1397_, lean_object* v_declHint_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1397_, v_declHint_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1405_, lean_object* v_ref_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1414_, v_ref_1415_, v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v_ref_1415_);
return v_res_1422_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_unsigned_to_nat(32u);
v___x_1424_ = lean_mk_empty_array_with_capacity(v___x_1423_);
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = ((size_t)5ULL);
v___x_1427_ = lean_unsigned_to_nat(0u);
v___x_1428_ = lean_unsigned_to_nat(32u);
v___x_1429_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___x_1430_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1431_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v___x_1429_);
lean_ctor_set(v___x_1431_, 2, v___x_1427_);
lean_ctor_set(v___x_1431_, 3, v___x_1427_);
lean_ctor_set_usize(v___x_1431_, 4, v___x_1426_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; lean_object* v_traceState_1435_; lean_object* v_traces_1436_; lean_object* v___x_1437_; lean_object* v_traceState_1438_; lean_object* v_env_1439_; lean_object* v_nextMacroScope_1440_; lean_object* v_ngen_1441_; lean_object* v_auxDeclNGen_1442_; lean_object* v_cache_1443_; lean_object* v_messages_1444_; lean_object* v_infoState_1445_; lean_object* v_snapshotTasks_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1465_; 
v___x_1434_ = lean_st_ref_get(v___y_1432_);
v_traceState_1435_ = lean_ctor_get(v___x_1434_, 4);
lean_inc_ref(v_traceState_1435_);
lean_dec(v___x_1434_);
v_traces_1436_ = lean_ctor_get(v_traceState_1435_, 0);
lean_inc_ref(v_traces_1436_);
lean_dec_ref(v_traceState_1435_);
v___x_1437_ = lean_st_ref_take(v___y_1432_);
v_traceState_1438_ = lean_ctor_get(v___x_1437_, 4);
v_env_1439_ = lean_ctor_get(v___x_1437_, 0);
v_nextMacroScope_1440_ = lean_ctor_get(v___x_1437_, 1);
v_ngen_1441_ = lean_ctor_get(v___x_1437_, 2);
v_auxDeclNGen_1442_ = lean_ctor_get(v___x_1437_, 3);
v_cache_1443_ = lean_ctor_get(v___x_1437_, 5);
v_messages_1444_ = lean_ctor_get(v___x_1437_, 6);
v_infoState_1445_ = lean_ctor_get(v___x_1437_, 7);
v_snapshotTasks_1446_ = lean_ctor_get(v___x_1437_, 8);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1448_ = v___x_1437_;
v_isShared_1449_ = v_isSharedCheck_1465_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_snapshotTasks_1446_);
lean_inc(v_infoState_1445_);
lean_inc(v_messages_1444_);
lean_inc(v_cache_1443_);
lean_inc(v_traceState_1438_);
lean_inc(v_auxDeclNGen_1442_);
lean_inc(v_ngen_1441_);
lean_inc(v_nextMacroScope_1440_);
lean_inc(v_env_1439_);
lean_dec(v___x_1437_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1465_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
uint64_t v_tid_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1463_; 
v_tid_1450_ = lean_ctor_get_uint64(v_traceState_1438_, sizeof(void*)*1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_traceState_1438_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_traceState_1438_, 0);
lean_dec(v_unused_1464_);
v___x_1452_ = v_traceState_1438_;
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_traceState_1438_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1454_);
lean_ctor_set_uint64(v_reuseFailAlloc_1462_, sizeof(void*)*1, v_tid_1450_);
v___x_1456_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1458_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 4, v___x_1456_);
v___x_1458_ = v___x_1448_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_env_1439_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_nextMacroScope_1440_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_ngen_1441_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_auxDeclNGen_1442_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1461_, 5, v_cache_1443_);
lean_ctor_set(v_reuseFailAlloc_1461_, 6, v_messages_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 7, v_infoState_1445_);
lean_ctor_set(v_reuseFailAlloc_1461_, 8, v_snapshotTasks_1446_);
v___x_1458_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_st_ref_set(v___y_1432_, v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_traces_1436_);
return v___x_1460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1466_);
lean_dec(v___y_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1472_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1481_, lean_object* v_opt_1482_){
_start:
{
lean_object* v_name_1483_; lean_object* v_defValue_1484_; lean_object* v_map_1485_; lean_object* v___x_1486_; 
v_name_1483_ = lean_ctor_get(v_opt_1482_, 0);
v_defValue_1484_ = lean_ctor_get(v_opt_1482_, 1);
v_map_1485_ = lean_ctor_get(v_opts_1481_, 0);
v___x_1486_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1485_, v_name_1483_);
if (lean_obj_tag(v___x_1486_) == 0)
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_unbox(v_defValue_1484_);
return v___x_1487_;
}
else
{
lean_object* v_val_1488_; 
v_val_1488_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1486_, 1);
if (lean_obj_tag(v_val_1488_) == 1)
{
uint8_t v_v_1489_; 
v_v_1489_ = lean_ctor_get_uint8(v_val_1488_, 0);
lean_dec_ref_known(v_val_1488_, 0);
return v_v_1489_;
}
else
{
uint8_t v___x_1490_; 
lean_dec(v_val_1488_);
v___x_1490_ = lean_unbox(v_defValue_1484_);
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1491_, lean_object* v_opt_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1491_, v_opt_1492_);
lean_dec_ref(v_opt_1492_);
lean_dec_ref(v_opts_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_MessageData_ofName(v_indName_1495_);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1504_, lean_object* v_x_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_mkBelow___lam__0(v_indName_1504_, v_x_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec_ref(v_x_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1512_){
_start:
{
if (lean_obj_tag(v_e_1512_) == 0)
{
uint8_t v___x_1513_; 
v___x_1513_ = 2;
return v___x_1513_;
}
else
{
uint8_t v___x_1514_; 
v___x_1514_ = 0;
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1515_);
lean_dec_ref(v_e_1515_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1518_){
_start:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
v_a_1520_ = lean_ctor_get(v_x_1518_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v_x_1518_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v_x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 1);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
v_a_1528_ = lean_ctor_get(v_x_1518_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_x_1518_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v_x_1518_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v_x_1518_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 0);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1539_, lean_object* v_opt_1540_){
_start:
{
lean_object* v_name_1541_; lean_object* v_defValue_1542_; lean_object* v_map_1543_; lean_object* v___x_1544_; 
v_name_1541_ = lean_ctor_get(v_opt_1540_, 0);
v_defValue_1542_ = lean_ctor_get(v_opt_1540_, 1);
v_map_1543_ = lean_ctor_get(v_opts_1539_, 0);
v___x_1544_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1543_, v_name_1541_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_inc(v_defValue_1542_);
return v_defValue_1542_;
}
else
{
lean_object* v_val_1545_; 
v_val_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_val_1545_);
lean_dec_ref_known(v___x_1544_, 1);
if (lean_obj_tag(v_val_1545_) == 3)
{
lean_object* v_v_1546_; 
v_v_1546_ = lean_ctor_get(v_val_1545_, 0);
lean_inc(v_v_1546_);
lean_dec_ref_known(v_val_1545_, 1);
return v_v_1546_;
}
else
{
lean_dec(v_val_1545_);
lean_inc(v_defValue_1542_);
return v_defValue_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1547_, lean_object* v_opt_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1547_, v_opt_1548_);
lean_dec_ref(v_opt_1548_);
lean_dec_ref(v_opts_1547_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1550_, size_t v_i_1551_, lean_object* v_bs_1552_){
_start:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_lt(v_i_1551_, v_sz_1550_);
if (v___x_1553_ == 0)
{
return v_bs_1552_;
}
else
{
lean_object* v_v_1554_; lean_object* v_msg_1555_; lean_object* v___x_1556_; lean_object* v_bs_x27_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_v_1554_ = lean_array_uget_borrowed(v_bs_1552_, v_i_1551_);
v_msg_1555_ = lean_ctor_get(v_v_1554_, 1);
lean_inc_ref(v_msg_1555_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v_bs_x27_1557_ = lean_array_uset(v_bs_1552_, v_i_1551_, v___x_1556_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1551_, v___x_1558_);
v___x_1560_ = lean_array_uset(v_bs_x27_1557_, v_i_1551_, v_msg_1555_);
v_i_1551_ = v___x_1559_;
v_bs_1552_ = v___x_1560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_bs_1564_){
_start:
{
size_t v_sz_boxed_1565_; size_t v_i_boxed_1566_; lean_object* v_res_1567_; 
v_sz_boxed_1565_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1566_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1565_, v_i_boxed_1566_, v_bs_1564_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1568_, lean_object* v_data_1569_, lean_object* v_ref_1570_, lean_object* v_msg_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_fileName_1577_; lean_object* v_fileMap_1578_; lean_object* v_options_1579_; lean_object* v_currRecDepth_1580_; lean_object* v_maxRecDepth_1581_; lean_object* v_ref_1582_; lean_object* v_currNamespace_1583_; lean_object* v_openDecls_1584_; lean_object* v_initHeartbeats_1585_; lean_object* v_maxHeartbeats_1586_; lean_object* v_quotContext_1587_; lean_object* v_currMacroScope_1588_; uint8_t v_diag_1589_; lean_object* v_cancelTk_x3f_1590_; uint8_t v_suppressElabErrors_1591_; lean_object* v_inheritedTraceOptions_1592_; lean_object* v___x_1593_; lean_object* v_traceState_1594_; lean_object* v_traces_1595_; lean_object* v_ref_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; lean_object* v_msg_1602_; lean_object* v___x_1603_; lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1641_; 
v_fileName_1577_ = lean_ctor_get(v___y_1574_, 0);
v_fileMap_1578_ = lean_ctor_get(v___y_1574_, 1);
v_options_1579_ = lean_ctor_get(v___y_1574_, 2);
v_currRecDepth_1580_ = lean_ctor_get(v___y_1574_, 3);
v_maxRecDepth_1581_ = lean_ctor_get(v___y_1574_, 4);
v_ref_1582_ = lean_ctor_get(v___y_1574_, 5);
v_currNamespace_1583_ = lean_ctor_get(v___y_1574_, 6);
v_openDecls_1584_ = lean_ctor_get(v___y_1574_, 7);
v_initHeartbeats_1585_ = lean_ctor_get(v___y_1574_, 8);
v_maxHeartbeats_1586_ = lean_ctor_get(v___y_1574_, 9);
v_quotContext_1587_ = lean_ctor_get(v___y_1574_, 10);
v_currMacroScope_1588_ = lean_ctor_get(v___y_1574_, 11);
v_diag_1589_ = lean_ctor_get_uint8(v___y_1574_, sizeof(void*)*14);
v_cancelTk_x3f_1590_ = lean_ctor_get(v___y_1574_, 12);
v_suppressElabErrors_1591_ = lean_ctor_get_uint8(v___y_1574_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1592_ = lean_ctor_get(v___y_1574_, 13);
v___x_1593_ = lean_st_ref_get(v___y_1575_);
v_traceState_1594_ = lean_ctor_get(v___x_1593_, 4);
lean_inc_ref(v_traceState_1594_);
lean_dec(v___x_1593_);
v_traces_1595_ = lean_ctor_get(v_traceState_1594_, 0);
lean_inc_ref(v_traces_1595_);
lean_dec_ref(v_traceState_1594_);
v_ref_1596_ = l_Lean_replaceRef(v_ref_1570_, v_ref_1582_);
lean_inc_ref(v_inheritedTraceOptions_1592_);
lean_inc(v_cancelTk_x3f_1590_);
lean_inc(v_currMacroScope_1588_);
lean_inc(v_quotContext_1587_);
lean_inc(v_maxHeartbeats_1586_);
lean_inc(v_initHeartbeats_1585_);
lean_inc(v_openDecls_1584_);
lean_inc(v_currNamespace_1583_);
lean_inc(v_maxRecDepth_1581_);
lean_inc(v_currRecDepth_1580_);
lean_inc_ref(v_options_1579_);
lean_inc_ref(v_fileMap_1578_);
lean_inc_ref(v_fileName_1577_);
v___x_1597_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1597_, 0, v_fileName_1577_);
lean_ctor_set(v___x_1597_, 1, v_fileMap_1578_);
lean_ctor_set(v___x_1597_, 2, v_options_1579_);
lean_ctor_set(v___x_1597_, 3, v_currRecDepth_1580_);
lean_ctor_set(v___x_1597_, 4, v_maxRecDepth_1581_);
lean_ctor_set(v___x_1597_, 5, v_ref_1596_);
lean_ctor_set(v___x_1597_, 6, v_currNamespace_1583_);
lean_ctor_set(v___x_1597_, 7, v_openDecls_1584_);
lean_ctor_set(v___x_1597_, 8, v_initHeartbeats_1585_);
lean_ctor_set(v___x_1597_, 9, v_maxHeartbeats_1586_);
lean_ctor_set(v___x_1597_, 10, v_quotContext_1587_);
lean_ctor_set(v___x_1597_, 11, v_currMacroScope_1588_);
lean_ctor_set(v___x_1597_, 12, v_cancelTk_x3f_1590_);
lean_ctor_set(v___x_1597_, 13, v_inheritedTraceOptions_1592_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14, v_diag_1589_);
lean_ctor_set_uint8(v___x_1597_, sizeof(void*)*14 + 1, v_suppressElabErrors_1591_);
v___x_1598_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1595_);
lean_dec_ref(v_traces_1595_);
v_sz_1599_ = lean_array_size(v___x_1598_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1599_, v___x_1600_, v___x_1598_);
v_msg_1602_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1602_, 0, v_data_1569_);
lean_ctor_set(v_msg_1602_, 1, v_msg_1571_);
lean_ctor_set(v_msg_1602_, 2, v___x_1601_);
v___x_1603_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1602_, v___y_1572_, v___y_1573_, v___x_1597_, v___y_1575_);
lean_dec_ref_known(v___x_1597_, 14);
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1641_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1641_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v_traceState_1609_; lean_object* v_env_1610_; lean_object* v_nextMacroScope_1611_; lean_object* v_ngen_1612_; lean_object* v_auxDeclNGen_1613_; lean_object* v_cache_1614_; lean_object* v_messages_1615_; lean_object* v_infoState_1616_; lean_object* v_snapshotTasks_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1640_; 
v___x_1608_ = lean_st_ref_take(v___y_1575_);
v_traceState_1609_ = lean_ctor_get(v___x_1608_, 4);
v_env_1610_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1611_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1612_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1613_ = lean_ctor_get(v___x_1608_, 3);
v_cache_1614_ = lean_ctor_get(v___x_1608_, 5);
v_messages_1615_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1616_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1617_ = lean_ctor_get(v___x_1608_, 8);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1619_ = v___x_1608_;
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snapshotTasks_1617_);
lean_inc(v_infoState_1616_);
lean_inc(v_messages_1615_);
lean_inc(v_cache_1614_);
lean_inc(v_traceState_1609_);
lean_inc(v_auxDeclNGen_1613_);
lean_inc(v_ngen_1612_);
lean_inc(v_nextMacroScope_1611_);
lean_inc(v_env_1610_);
lean_dec(v___x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1640_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
uint64_t v_tid_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1638_; 
v_tid_1621_ = lean_ctor_get_uint64(v_traceState_1609_, sizeof(void*)*1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_traceState_1609_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v_traceState_1609_, 0);
lean_dec(v_unused_1639_);
v___x_1623_ = v_traceState_1609_;
v_isShared_1624_ = v_isSharedCheck_1638_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_traceState_1609_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1638_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_ref_1570_);
lean_ctor_set(v___x_1625_, 1, v_a_1604_);
v___x_1626_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1568_, v___x_1625_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1626_);
lean_ctor_set_uint64(v_reuseFailAlloc_1637_, sizeof(void*)*1, v_tid_1621_);
v___x_1628_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1630_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___x_1628_);
v___x_1630_ = v___x_1619_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_env_1610_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_nextMacroScope_1611_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_ngen_1612_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_auxDeclNGen_1613_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1636_, 5, v_cache_1614_);
lean_ctor_set(v_reuseFailAlloc_1636_, 6, v_messages_1615_);
lean_ctor_set(v_reuseFailAlloc_1636_, 7, v_infoState_1616_);
lean_ctor_set(v_reuseFailAlloc_1636_, 8, v_snapshotTasks_1617_);
v___x_1630_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1631_ = lean_st_ref_set(v___y_1575_, v___x_1630_);
v___x_1632_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1632_);
v___x_1634_ = v___x_1606_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1642_, lean_object* v_data_1643_, lean_object* v_ref_1644_, lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1642_, v_data_1643_, v_ref_1644_, v_msg_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1651_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1652_; double v___x_1653_; 
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = lean_float_of_nat(v___x_1652_);
return v___x_1653_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1656_ = l_Lean_stringToMessageData(v___x_1655_);
return v___x_1656_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1657_; double v___x_1658_; 
v___x_1657_ = lean_unsigned_to_nat(1000u);
v___x_1658_ = lean_float_of_nat(v___x_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1659_, uint8_t v_collapsed_1660_, lean_object* v_tag_1661_, lean_object* v_opts_1662_, uint8_t v_clsEnabled_1663_, lean_object* v_oldTraces_1664_, lean_object* v_msg_1665_, lean_object* v_resStartStop_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_fst_1672_; lean_object* v_snd_1673_; lean_object* v___y_1675_; lean_object* v___y_1676_; lean_object* v_data_1677_; lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; lean_object* v___y_1685_; lean_object* v_a_1686_; uint8_t v___y_1701_; double v___y_1732_; 
v_fst_1672_ = lean_ctor_get(v_resStartStop_1666_, 0);
lean_inc(v_fst_1672_);
v_snd_1673_ = lean_ctor_get(v_resStartStop_1666_, 1);
lean_inc(v_snd_1673_);
lean_dec_ref(v_resStartStop_1666_);
v_fst_1680_ = lean_ctor_get(v_snd_1673_, 0);
lean_inc(v_fst_1680_);
v_snd_1681_ = lean_ctor_get(v_snd_1673_, 1);
lean_inc(v_snd_1681_);
lean_dec(v_snd_1673_);
v___x_1682_ = l_Lean_trace_profiler;
v___x_1683_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1662_, v___x_1682_);
if (v___x_1683_ == 0)
{
v___y_1701_ = v___x_1683_;
goto v___jp_1700_;
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1738_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1662_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; double v___x_1741_; double v___x_1742_; double v___x_1743_; 
v___x_1739_ = l_Lean_trace_profiler_threshold;
v___x_1740_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1662_, v___x_1739_);
v___x_1741_ = lean_float_of_nat(v___x_1740_);
v___x_1742_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1743_ = lean_float_div(v___x_1741_, v___x_1742_);
v___y_1732_ = v___x_1743_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; double v___x_1746_; 
v___x_1744_ = l_Lean_trace_profiler_threshold;
v___x_1745_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1662_, v___x_1744_);
v___x_1746_ = lean_float_of_nat(v___x_1745_);
v___y_1732_ = v___x_1746_;
goto v___jp_1731_;
}
}
v___jp_1674_:
{
lean_object* v___x_1678_; 
lean_inc(v___y_1676_);
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1664_, v_data_1677_, v___y_1676_, v___y_1675_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v___x_1679_; 
lean_dec_ref_known(v___x_1678_, 1);
v___x_1679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1672_);
return v___x_1679_;
}
else
{
lean_dec(v_fst_1672_);
return v___x_1678_;
}
}
v___jp_1684_:
{
uint8_t v_result_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; double v___x_1690_; lean_object* v_data_1691_; 
v_result_1687_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1672_);
v___x_1688_ = lean_box(v_result_1687_);
v___x_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
v___x_1690_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1661_);
lean_inc_ref(v___x_1689_);
lean_inc(v_cls_1659_);
v_data_1691_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1691_, 0, v_cls_1659_);
lean_ctor_set(v_data_1691_, 1, v___x_1689_);
lean_ctor_set(v_data_1691_, 2, v_tag_1661_);
lean_ctor_set_float(v_data_1691_, sizeof(void*)*3, v___x_1690_);
lean_ctor_set_float(v_data_1691_, sizeof(void*)*3 + 8, v___x_1690_);
lean_ctor_set_uint8(v_data_1691_, sizeof(void*)*3 + 16, v_collapsed_1660_);
if (v___x_1683_ == 0)
{
lean_dec_ref_known(v___x_1689_, 1);
lean_dec(v_snd_1681_);
lean_dec(v_fst_1680_);
lean_dec_ref(v_tag_1661_);
lean_dec(v_cls_1659_);
v___y_1675_ = v_a_1686_;
v___y_1676_ = v___y_1685_;
v_data_1677_ = v_data_1691_;
goto v___jp_1674_;
}
else
{
lean_object* v_data_1692_; double v___x_1693_; double v___x_1694_; 
lean_dec_ref_known(v_data_1691_, 3);
v_data_1692_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1692_, 0, v_cls_1659_);
lean_ctor_set(v_data_1692_, 1, v___x_1689_);
lean_ctor_set(v_data_1692_, 2, v_tag_1661_);
v___x_1693_ = lean_unbox_float(v_fst_1680_);
lean_dec(v_fst_1680_);
lean_ctor_set_float(v_data_1692_, sizeof(void*)*3, v___x_1693_);
v___x_1694_ = lean_unbox_float(v_snd_1681_);
lean_dec(v_snd_1681_);
lean_ctor_set_float(v_data_1692_, sizeof(void*)*3 + 8, v___x_1694_);
lean_ctor_set_uint8(v_data_1692_, sizeof(void*)*3 + 16, v_collapsed_1660_);
v___y_1675_ = v_a_1686_;
v___y_1676_ = v___y_1685_;
v_data_1677_ = v_data_1692_;
goto v___jp_1674_;
}
}
v___jp_1695_:
{
lean_object* v_ref_1696_; lean_object* v___x_1697_; 
v_ref_1696_ = lean_ctor_get(v___y_1669_, 5);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v_fst_1672_);
v___x_1697_ = lean_apply_6(v_msg_1665_, v_fst_1672_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, lean_box(0));
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
v___y_1685_ = v_ref_1696_;
v_a_1686_ = v_a_1698_;
goto v___jp_1684_;
}
else
{
lean_object* v___x_1699_; 
lean_dec_ref_known(v___x_1697_, 1);
v___x_1699_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1685_ = v_ref_1696_;
v_a_1686_ = v___x_1699_;
goto v___jp_1684_;
}
}
v___jp_1700_:
{
if (v_clsEnabled_1663_ == 0)
{
if (v___y_1701_ == 0)
{
lean_object* v___x_1702_; lean_object* v_traceState_1703_; lean_object* v_env_1704_; lean_object* v_nextMacroScope_1705_; lean_object* v_ngen_1706_; lean_object* v_auxDeclNGen_1707_; lean_object* v_cache_1708_; lean_object* v_messages_1709_; lean_object* v_infoState_1710_; lean_object* v_snapshotTasks_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_snd_1681_);
lean_dec(v_fst_1680_);
lean_dec_ref(v_msg_1665_);
lean_dec_ref(v_tag_1661_);
lean_dec(v_cls_1659_);
v___x_1702_ = lean_st_ref_take(v___y_1670_);
v_traceState_1703_ = lean_ctor_get(v___x_1702_, 4);
v_env_1704_ = lean_ctor_get(v___x_1702_, 0);
v_nextMacroScope_1705_ = lean_ctor_get(v___x_1702_, 1);
v_ngen_1706_ = lean_ctor_get(v___x_1702_, 2);
v_auxDeclNGen_1707_ = lean_ctor_get(v___x_1702_, 3);
v_cache_1708_ = lean_ctor_get(v___x_1702_, 5);
v_messages_1709_ = lean_ctor_get(v___x_1702_, 6);
v_infoState_1710_ = lean_ctor_get(v___x_1702_, 7);
v_snapshotTasks_1711_ = lean_ctor_get(v___x_1702_, 8);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1713_ = v___x_1702_;
v_isShared_1714_ = v_isSharedCheck_1730_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_snapshotTasks_1711_);
lean_inc(v_infoState_1710_);
lean_inc(v_messages_1709_);
lean_inc(v_cache_1708_);
lean_inc(v_traceState_1703_);
lean_inc(v_auxDeclNGen_1707_);
lean_inc(v_ngen_1706_);
lean_inc(v_nextMacroScope_1705_);
lean_inc(v_env_1704_);
lean_dec(v___x_1702_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1730_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint64_t v_tid_1715_; lean_object* v_traces_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1729_; 
v_tid_1715_ = lean_ctor_get_uint64(v_traceState_1703_, sizeof(void*)*1);
v_traces_1716_ = lean_ctor_get(v_traceState_1703_, 0);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_traceState_1703_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1718_ = v_traceState_1703_;
v_isShared_1719_ = v_isSharedCheck_1729_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_traces_1716_);
lean_dec(v_traceState_1703_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1729_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1664_, v_traces_1716_);
lean_dec_ref(v_traces_1716_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1720_);
lean_ctor_set_uint64(v_reuseFailAlloc_1728_, sizeof(void*)*1, v_tid_1715_);
v___x_1722_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 4, v___x_1722_);
v___x_1724_ = v___x_1713_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_env_1704_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_nextMacroScope_1705_);
lean_ctor_set(v_reuseFailAlloc_1727_, 2, v_ngen_1706_);
lean_ctor_set(v_reuseFailAlloc_1727_, 3, v_auxDeclNGen_1707_);
lean_ctor_set(v_reuseFailAlloc_1727_, 4, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1727_, 5, v_cache_1708_);
lean_ctor_set(v_reuseFailAlloc_1727_, 6, v_messages_1709_);
lean_ctor_set(v_reuseFailAlloc_1727_, 7, v_infoState_1710_);
lean_ctor_set(v_reuseFailAlloc_1727_, 8, v_snapshotTasks_1711_);
v___x_1724_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_st_ref_set(v___y_1670_, v___x_1724_);
v___x_1726_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1672_);
return v___x_1726_;
}
}
}
}
}
else
{
goto v___jp_1695_;
}
}
else
{
goto v___jp_1695_;
}
}
v___jp_1731_:
{
double v___x_1733_; double v___x_1734_; double v___x_1735_; uint8_t v___x_1736_; 
v___x_1733_ = lean_unbox_float(v_snd_1681_);
v___x_1734_ = lean_unbox_float(v_fst_1680_);
v___x_1735_ = lean_float_sub(v___x_1733_, v___x_1734_);
v___x_1736_ = lean_float_decLt(v___y_1732_, v___x_1735_);
v___y_1701_ = v___x_1736_;
goto v___jp_1700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1747_, lean_object* v_collapsed_1748_, lean_object* v_tag_1749_, lean_object* v_opts_1750_, lean_object* v_clsEnabled_1751_, lean_object* v_oldTraces_1752_, lean_object* v_msg_1753_, lean_object* v_resStartStop_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
uint8_t v_collapsed_boxed_1760_; uint8_t v_clsEnabled_boxed_1761_; lean_object* v_res_1762_; 
v_collapsed_boxed_1760_ = lean_unbox(v_collapsed_1748_);
v_clsEnabled_boxed_1761_ = lean_unbox(v_clsEnabled_1751_);
v_res_1762_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1747_, v_collapsed_boxed_1760_, v_tag_1749_, v_opts_1750_, v_clsEnabled_boxed_1761_, v_oldTraces_1752_, v_msg_1753_, v_resStartStop_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v_opts_1750_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v___x_1766_, lean_object* v_a_1767_, lean_object* v_b_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_lt(v_a_1767_, v_upperBound_1763_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; 
lean_dec(v_a_1767_);
lean_dec(v___x_1766_);
lean_dec(v___x_1765_);
lean_dec(v___x_1764_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v_b_1768_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_a_1767_, v___x_1776_);
lean_dec(v_a_1767_);
lean_inc_n(v___x_1777_, 2);
lean_inc(v___x_1764_);
v___x_1778_ = lean_name_append_index_after(v___x_1764_, v___x_1777_);
lean_inc(v___x_1765_);
v___x_1779_ = lean_name_append_index_after(v___x_1765_, v___x_1777_);
lean_inc(v___x_1766_);
v___x_1780_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1778_, v___x_1766_, v___x_1779_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref_known(v___x_1780_, 1);
v___x_1781_ = lean_box(0);
v_a_1767_ = v___x_1777_;
v_b_1768_ = v___x_1781_;
goto _start;
}
else
{
lean_dec(v___x_1777_);
lean_dec(v___x_1766_);
lean_dec(v___x_1765_);
lean_dec(v___x_1764_);
return v___x_1780_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v___x_1786_, lean_object* v_a_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1783_, v___x_1784_, v___x_1785_, v___x_1786_, v_a_1787_, v_b_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v_upperBound_1783_);
return v_res_1794_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1805_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1806_ = l_Lean_Name_append(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1807_; double v___x_1808_; 
v___x_1807_ = lean_unsigned_to_nat(1000000000u);
v___x_1808_ = lean_float_of_nat(v___x_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_options_1815_; uint8_t v_hasTrace_1816_; 
v_options_1815_ = lean_ctor_get(v_a_1812_, 2);
v_hasTrace_1816_ = lean_ctor_get_uint8(v_options_1815_, sizeof(void*)*1);
if (v_hasTrace_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_inc(v_indName_1809_);
v___x_1817_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1882_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1882_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1882_;
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
lean_dec(v_indName_1809_);
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
v___x_1833_ = l_Lean_Meta_isPropFormerType(v_type_1832_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1869_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1869_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1869_;
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
lean_inc_n(v_indName_1809_, 2);
v___x_1839_ = l_Lean_mkRecName(v_indName_1809_);
v___x_1840_ = l_Lean_mkBelowName(v_indName_1809_);
lean_inc(v___x_1840_);
lean_inc(v_numParams_1829_);
lean_inc(v___x_1839_);
v___x_1841_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1839_, v_numParams_1829_, v___x_1840_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1863_; 
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1864_);
v___x_1843_ = v___x_1841_;
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
else
{
lean_dec(v___x_1841_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1863_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = l_List_get_x21Internal___redArg(v___x_1845_, v_all_1830_, v___x_1846_);
lean_dec(v_all_1830_);
v___x_1848_ = lean_name_eq(v___x_1847_, v_indName_1809_);
lean_dec(v_indName_1809_);
lean_dec(v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v___x_1840_);
lean_dec(v___x_1839_);
lean_dec(v_numNested_1831_);
lean_dec(v_numParams_1829_);
v___x_1849_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1849_);
v___x_1851_ = v___x_1843_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_del_object(v___x_1843_);
v___x_1853_ = lean_box(0);
v___x_1854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1831_, v___x_1839_, v___x_1840_, v_numParams_1829_, v___x_1846_, v___x_1853_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_numNested_1831_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v___x_1854_, 0);
lean_dec(v_unused_1862_);
v___x_1856_ = v___x_1854_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_dec(v___x_1854_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1853_);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1853_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
return v___x_1854_;
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
lean_dec(v_indName_1809_);
return v___x_1841_;
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_numNested_1831_);
lean_dec(v_all_1830_);
lean_dec(v_numParams_1829_);
lean_dec(v_indName_1809_);
v___x_1865_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1865_);
v___x_1867_ = v___x_1836_;
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
lean_dec(v_numNested_1831_);
lean_dec(v_all_1830_);
lean_dec(v_numParams_1829_);
lean_dec(v_indName_1809_);
v_a_1870_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1833_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1833_);
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
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1880_; 
lean_dec(v_a_1818_);
lean_dec(v_indName_1809_);
v___x_1878_ = lean_box(0);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1878_);
v___x_1880_ = v___x_1820_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_indName_1809_);
v_a_1883_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1817_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1817_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
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
lean_object* v_inheritedTraceOptions_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v_a_1900_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v_a_1915_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v_a_1920_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v_a_1925_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v_a_1937_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v_a_1942_; 
v_inheritedTraceOptions_1891_ = lean_ctor_get(v_a_1812_, 13);
lean_inc(v_indName_1809_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1892_, 0, v_indName_1809_);
v___x_1893_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1894_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1895_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1891_, v_options_1815_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = l_Lean_trace_profiler;
v___x_2012_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1815_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; 
lean_dec_ref(v___f_1892_);
lean_inc(v_indName_1809_);
v___x_2013_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2078_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2078_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2078_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
if (lean_obj_tag(v_a_2014_) == 5)
{
lean_object* v_val_2018_; uint8_t v_isRec_2019_; 
v_val_2018_ = lean_ctor_get(v_a_2014_, 0);
lean_inc_ref(v_val_2018_);
lean_dec_ref_known(v_a_2014_, 1);
v_isRec_2019_ = lean_ctor_get_uint8(v_val_2018_, sizeof(void*)*6);
if (v_isRec_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec_ref(v_val_2018_);
lean_dec(v_indName_1809_);
v___x_2020_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2020_);
v___x_2022_ = v___x_2016_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v_toConstantVal_2024_; lean_object* v_numParams_2025_; lean_object* v_all_2026_; lean_object* v_numNested_2027_; lean_object* v_type_2028_; lean_object* v___x_2029_; 
lean_del_object(v___x_2016_);
v_toConstantVal_2024_ = lean_ctor_get(v_val_2018_, 0);
lean_inc_ref(v_toConstantVal_2024_);
v_numParams_2025_ = lean_ctor_get(v_val_2018_, 1);
lean_inc(v_numParams_2025_);
v_all_2026_ = lean_ctor_get(v_val_2018_, 3);
lean_inc(v_all_2026_);
v_numNested_2027_ = lean_ctor_get(v_val_2018_, 5);
lean_inc(v_numNested_2027_);
lean_dec_ref(v_val_2018_);
v_type_2028_ = lean_ctor_get(v_toConstantVal_2024_, 2);
lean_inc_ref(v_type_2028_);
lean_dec_ref(v_toConstantVal_2024_);
v___x_2029_ = l_Lean_Meta_isPropFormerType(v_type_2028_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2065_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2065_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2065_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_del_object(v___x_2032_);
lean_inc_n(v_indName_1809_, 2);
v___x_2035_ = l_Lean_mkRecName(v_indName_1809_);
v___x_2036_ = l_Lean_mkBelowName(v_indName_1809_);
lean_inc(v___x_2036_);
lean_inc(v_numParams_2025_);
lean_inc(v___x_2035_);
v___x_2037_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2035_, v_numParams_2025_, v___x_2036_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2059_; 
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2037_, 0);
lean_dec(v_unused_2060_);
v___x_2039_ = v___x_2037_;
v_isShared_2040_ = v_isSharedCheck_2059_;
goto v_resetjp_2038_;
}
else
{
lean_dec(v___x_2037_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2059_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = l_List_get_x21Internal___redArg(v___x_2041_, v_all_2026_, v___x_2042_);
lean_dec(v_all_2026_);
v___x_2044_ = lean_name_eq(v___x_2043_, v_indName_1809_);
lean_dec(v_indName_1809_);
lean_dec(v___x_2043_);
if (v___x_2044_ == 0)
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v___x_2036_);
lean_dec(v___x_2035_);
lean_dec(v_numNested_2027_);
lean_dec(v_numParams_2025_);
v___x_2045_ = lean_box(0);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2045_);
v___x_2047_ = v___x_2039_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_del_object(v___x_2039_);
v___x_2049_ = lean_box(0);
v___x_2050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2027_, v___x_2035_, v___x_2036_, v_numParams_2025_, v___x_2042_, v___x_2049_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_numNested_2027_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2050_, 0);
lean_dec(v_unused_2058_);
v___x_2052_ = v___x_2050_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_dec(v___x_2050_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 0, v___x_2049_);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2049_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
return v___x_2050_;
}
}
}
}
else
{
lean_dec(v___x_2036_);
lean_dec(v___x_2035_);
lean_dec(v_numNested_2027_);
lean_dec(v_all_2026_);
lean_dec(v_numParams_2025_);
lean_dec(v_indName_1809_);
return v___x_2037_;
}
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_dec(v_numNested_2027_);
lean_dec(v_all_2026_);
lean_dec(v_numParams_2025_);
lean_dec(v_indName_1809_);
v___x_2061_ = lean_box(0);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2061_);
v___x_2063_ = v___x_2032_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_numNested_2027_);
lean_dec(v_all_2026_);
lean_dec(v_numParams_2025_);
lean_dec(v_indName_1809_);
v_a_2066_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2029_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2029_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_dec(v_a_2014_);
lean_dec(v_indName_1809_);
v___x_2074_ = lean_box(0);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2074_);
v___x_2076_ = v___x_2016_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_indName_1809_);
v_a_2079_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2013_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2013_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
goto v___jp_1944_;
}
}
else
{
goto v___jp_1944_;
}
v___jp_1897_:
{
lean_object* v___x_1901_; double v___x_1902_; double v___x_1903_; double v___x_1904_; double v___x_1905_; double v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1901_ = lean_io_mono_nanos_now();
v___x_1902_ = lean_float_of_nat(v___y_1899_);
v___x_1903_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1904_ = lean_float_div(v___x_1902_, v___x_1903_);
v___x_1905_ = lean_float_of_nat(v___x_1901_);
v___x_1906_ = lean_float_div(v___x_1905_, v___x_1903_);
v___x_1907_ = lean_box_float(v___x_1904_);
v___x_1908_ = lean_box_float(v___x_1906_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_a_1900_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1893_, v_hasTrace_1816_, v___x_1894_, v_options_1815_, v___x_1896_, v___y_1898_, v___f_1892_, v___x_1910_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1911_;
}
v___jp_1912_:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_a_1915_);
v___y_1898_ = v___y_1913_;
v___y_1899_ = v___y_1914_;
v_a_1900_ = v___x_1916_;
goto v___jp_1897_;
}
v___jp_1917_:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1920_);
v___y_1898_ = v___y_1918_;
v___y_1899_ = v___y_1919_;
v_a_1900_ = v___x_1921_;
goto v___jp_1897_;
}
v___jp_1922_:
{
lean_object* v___x_1926_; double v___x_1927_; double v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1926_ = lean_io_get_num_heartbeats();
v___x_1927_ = lean_float_of_nat(v___y_1924_);
v___x_1928_ = lean_float_of_nat(v___x_1926_);
v___x_1929_ = lean_box_float(v___x_1927_);
v___x_1930_ = lean_box_float(v___x_1928_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1925_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1893_, v_hasTrace_1816_, v___x_1894_, v_options_1815_, v___x_1896_, v___y_1923_, v___f_1892_, v___x_1932_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1933_;
}
v___jp_1934_:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1937_);
v___y_1923_ = v___y_1935_;
v___y_1924_ = v___y_1936_;
v_a_1925_ = v___x_1938_;
goto v___jp_1922_;
}
v___jp_1939_:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_a_1942_);
v___y_1923_ = v___y_1940_;
v___y_1924_ = v___y_1941_;
v_a_1925_ = v___x_1943_;
goto v___jp_1922_;
}
v___jp_1944_:
{
lean_object* v___x_1945_; lean_object* v_a_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v___x_1945_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1813_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1948_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1815_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1809_);
v___x_1950_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
if (lean_obj_tag(v_a_1951_) == 5)
{
lean_object* v_val_1952_; uint8_t v_isRec_1953_; 
v_val_1952_ = lean_ctor_get(v_a_1951_, 0);
lean_inc_ref(v_val_1952_);
lean_dec_ref_known(v_a_1951_, 1);
v_isRec_1953_ = lean_ctor_get_uint8(v_val_1952_, sizeof(void*)*6);
if (v_isRec_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref(v_val_1952_);
lean_dec(v_indName_1809_);
v___x_1954_ = lean_box(0);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v___x_1954_;
goto v___jp_1912_;
}
else
{
lean_object* v_toConstantVal_1955_; lean_object* v_numParams_1956_; lean_object* v_all_1957_; lean_object* v_numNested_1958_; lean_object* v_type_1959_; lean_object* v___x_1960_; 
v_toConstantVal_1955_ = lean_ctor_get(v_val_1952_, 0);
lean_inc_ref(v_toConstantVal_1955_);
v_numParams_1956_ = lean_ctor_get(v_val_1952_, 1);
lean_inc(v_numParams_1956_);
v_all_1957_ = lean_ctor_get(v_val_1952_, 3);
lean_inc(v_all_1957_);
v_numNested_1958_ = lean_ctor_get(v_val_1952_, 5);
lean_inc(v_numNested_1958_);
lean_dec_ref(v_val_1952_);
v_type_1959_ = lean_ctor_get(v_toConstantVal_1955_, 2);
lean_inc_ref(v_type_1959_);
lean_dec_ref(v_toConstantVal_1955_);
v___x_1960_ = l_Lean_Meta_isPropFormerType(v_type_1959_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; uint8_t v___x_1962_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = lean_unbox(v_a_1961_);
lean_dec(v_a_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_n(v_indName_1809_, 2);
v___x_1963_ = l_Lean_mkRecName(v_indName_1809_);
v___x_1964_ = l_Lean_mkBelowName(v_indName_1809_);
lean_inc(v___x_1964_);
lean_inc(v_numParams_1956_);
lean_inc(v___x_1963_);
v___x_1965_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1963_, v_numParams_1956_, v___x_1964_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
lean_dec_ref_known(v___x_1965_, 1);
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1968_ = l_List_get_x21Internal___redArg(v___x_1966_, v_all_1957_, v___x_1967_);
lean_dec(v_all_1957_);
v___x_1969_ = lean_name_eq(v___x_1968_, v_indName_1809_);
lean_dec(v_indName_1809_);
lean_dec(v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
lean_dec(v_numNested_1958_);
lean_dec(v_numParams_1956_);
v___x_1970_ = lean_box(0);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v___x_1970_;
goto v___jp_1912_;
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_box(0);
v___x_1972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1958_, v___x_1963_, v___x_1964_, v_numParams_1956_, v___x_1967_, v___x_1971_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_numNested_1958_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_dec_ref_known(v___x_1972_, 1);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v___x_1971_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___y_1918_ = v_a_1946_;
v___y_1919_ = v___x_1949_;
v_a_1920_ = v_a_1973_;
goto v___jp_1917_;
}
}
}
else
{
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
lean_dec(v_numNested_1958_);
lean_dec(v_all_1957_);
lean_dec(v_numParams_1956_);
lean_dec(v_indName_1809_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v_a_1974_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1975_; 
v_a_1975_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1918_ = v_a_1946_;
v___y_1919_ = v___x_1949_;
v_a_1920_ = v_a_1975_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v___x_1976_; 
lean_dec(v_numNested_1958_);
lean_dec(v_all_1957_);
lean_dec(v_numParams_1956_);
lean_dec(v_indName_1809_);
v___x_1976_ = lean_box(0);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v___x_1976_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1977_; 
lean_dec(v_numNested_1958_);
lean_dec(v_all_1957_);
lean_dec(v_numParams_1956_);
lean_dec(v_indName_1809_);
v_a_1977_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1960_, 1);
v___y_1918_ = v_a_1946_;
v___y_1919_ = v___x_1949_;
v_a_1920_ = v_a_1977_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v___x_1978_; 
lean_dec(v_a_1951_);
lean_dec(v_indName_1809_);
v___x_1978_ = lean_box(0);
v___y_1913_ = v_a_1946_;
v___y_1914_ = v___x_1949_;
v_a_1915_ = v___x_1978_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1979_; 
lean_dec(v_indName_1809_);
v_a_1979_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1950_, 1);
v___y_1918_ = v_a_1946_;
v___y_1919_ = v___x_1949_;
v_a_1920_ = v_a_1979_;
goto v___jp_1917_;
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1809_);
v___x_1981_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
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
lean_dec(v_indName_1809_);
v___x_1985_ = lean_box(0);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v___x_1985_;
goto v___jp_1934_;
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
v___x_1991_ = l_Lean_Meta_isPropFormerType(v_type_1990_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
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
lean_inc_n(v_indName_1809_, 2);
v___x_1994_ = l_Lean_mkRecName(v_indName_1809_);
v___x_1995_ = l_Lean_mkBelowName(v_indName_1809_);
lean_inc(v___x_1995_);
lean_inc(v_numParams_1987_);
lean_inc(v___x_1994_);
v___x_1996_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1994_, v_numParams_1987_, v___x_1995_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
lean_dec_ref_known(v___x_1996_, 1);
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = l_List_get_x21Internal___redArg(v___x_1997_, v_all_1988_, v___x_1998_);
lean_dec(v_all_1988_);
v___x_2000_ = lean_name_eq(v___x_1999_, v_indName_1809_);
lean_dec(v_indName_1809_);
lean_dec(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; 
lean_dec(v___x_1995_);
lean_dec(v___x_1994_);
lean_dec(v_numNested_1989_);
lean_dec(v_numParams_1987_);
v___x_2001_ = lean_box(0);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v___x_2001_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1989_, v___x_1994_, v___x_1995_, v_numParams_1987_, v___x_1998_, v___x_2002_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
lean_dec(v_numNested_1989_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_dec_ref_known(v___x_2003_, 1);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v___x_2002_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_2004_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1940_ = v_a_1946_;
v___y_1941_ = v___x_1980_;
v_a_1942_ = v_a_2004_;
goto v___jp_1939_;
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
lean_dec(v_indName_1809_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v_a_2005_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_1996_, 1);
v___y_1940_ = v_a_1946_;
v___y_1941_ = v___x_1980_;
v_a_1942_ = v_a_2006_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_numNested_1989_);
lean_dec(v_all_1988_);
lean_dec(v_numParams_1987_);
lean_dec(v_indName_1809_);
v___x_2007_ = lean_box(0);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v___x_2007_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_2008_; 
lean_dec(v_numNested_1989_);
lean_dec(v_all_1988_);
lean_dec(v_numParams_1987_);
lean_dec(v_indName_1809_);
v_a_2008_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1940_ = v_a_1946_;
v___y_1941_ = v___x_1980_;
v_a_1942_ = v_a_2008_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_2009_; 
lean_dec(v_a_1982_);
lean_dec(v_indName_1809_);
v___x_2009_ = lean_box(0);
v___y_1935_ = v_a_1946_;
v___y_1936_ = v___x_1980_;
v_a_1937_ = v___x_2009_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_2010_; 
lean_dec(v_indName_1809_);
v_a_2010_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_1981_, 1);
v___y_1940_ = v_a_1946_;
v___y_1941_ = v___x_1980_;
v_a_1942_ = v_a_2010_;
goto v___jp_1939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_mkBelow(v_indName_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v___x_2097_, lean_object* v_inst_2098_, lean_object* v_R_2099_, lean_object* v_a_2100_, lean_object* v_b_2101_, lean_object* v_c_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2094_, v___x_2095_, v___x_2096_, v___x_2097_, v_a_2100_, v_b_2101_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2109_, lean_object* v___x_2110_, lean_object* v___x_2111_, lean_object* v___x_2112_, lean_object* v_inst_2113_, lean_object* v_R_2114_, lean_object* v_a_2115_, lean_object* v_b_2116_, lean_object* v_c_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2109_, v___x_2110_, v___x_2111_, v___x_2112_, v_inst_2113_, v_R_2114_, v_a_2115_, v_b_2116_, v_c_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v_upperBound_2109_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2124_, lean_object* v_x_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2125_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2132_, lean_object* v_x_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2132_, v_x_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
if (lean_obj_tag(v_a_2140_) == 0)
{
lean_object* v___x_2142_; 
v___x_2142_ = l_List_reverse___redArg(v_a_2141_);
return v___x_2142_;
}
else
{
lean_object* v_head_2143_; lean_object* v_tail_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2153_; 
v_head_2143_ = lean_ctor_get(v_a_2140_, 0);
v_tail_2144_ = lean_ctor_get(v_a_2140_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_a_2140_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2146_ = v_a_2140_;
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_tail_2144_);
lean_inc(v_head_2143_);
lean_dec(v_a_2140_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2153_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_MessageData_ofExpr(v_head_2143_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v_a_2141_);
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_a_2141_);
v___x_2150_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
v_a_2140_ = v_tail_2144_;
v_a_2141_ = v___x_2150_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2154_, lean_object* v_v_2155_, lean_object* v_i_2156_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_get_size(v_xs_2154_);
v___x_2158_ = lean_nat_dec_lt(v_i_2156_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
lean_dec(v_i_2156_);
v___x_2159_ = lean_box(0);
return v___x_2159_;
}
else
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = lean_array_fget_borrowed(v_xs_2154_, v_i_2156_);
v___x_2161_ = lean_expr_eqv(v___x_2160_, v_v_2155_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_unsigned_to_nat(1u);
v___x_2163_ = lean_nat_add(v_i_2156_, v___x_2162_);
lean_dec(v_i_2156_);
v_i_2156_ = v___x_2163_;
goto _start;
}
else
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_i_2156_);
return v___x_2165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2166_, lean_object* v_v_2167_, lean_object* v_i_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2166_, v_v_2167_, v_i_2168_);
lean_dec_ref(v_v_2167_);
lean_dec_ref(v_xs_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2170_, lean_object* v_v_2171_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2170_, v_v_2171_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2174_, lean_object* v_v_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2174_, v_v_2175_);
lean_dec_ref(v_v_2175_);
lean_dec_ref(v_xs_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2177_, lean_object* v_v_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2177_, v_v_2178_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_box(0);
return v___x_2180_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_val_2181_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2179_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_val_2181_);
lean_dec(v___x_2179_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_val_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2189_, lean_object* v_v_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2189_, v_v_2190_);
lean_dec_ref(v_v_2190_);
lean_dec_ref(v_xs_2189_);
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2198_, lean_object* v_prods_2199_, lean_object* v_motives_2200_, lean_object* v_fs_2201_, lean_object* v_minor__type_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_, lean_object* v_x_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
if (lean_obj_tag(v_x_2203_) == 5)
{
lean_object* v_fn_2211_; lean_object* v_arg_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v_fn_2211_ = lean_ctor_get(v_x_2203_, 0);
lean_inc_ref(v_fn_2211_);
v_arg_2212_ = lean_ctor_get(v_x_2203_, 1);
lean_inc_ref(v_arg_2212_);
lean_dec_ref_known(v_x_2203_, 2);
v___x_2213_ = lean_array_set(v_x_2204_, v_x_2205_, v_arg_2212_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = lean_nat_sub(v_x_2205_, v___x_2214_);
lean_dec(v_x_2205_);
v_x_2203_ = v_fn_2211_;
v_x_2204_ = v___x_2213_;
v_x_2205_ = v___x_2215_;
goto _start;
}
else
{
lean_object* v___x_2217_; 
lean_dec(v_x_2205_);
v___x_2217_ = l_Lean_Meta_PProdN_mk(v_rlvl_2198_, v_prods_2199_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v___x_2219_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v___x_2219_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2200_, v_x_2203_);
lean_dec_ref(v_x_2203_);
if (lean_obj_tag(v___x_2219_) == 1)
{
lean_object* v_val_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v_minor__type_2202_);
lean_dec_ref(v_motives_2200_);
v_val_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_val_2220_);
lean_dec_ref_known(v___x_2219_, 1);
v___x_2221_ = l_Lean_instInhabitedExpr;
v___x_2222_ = lean_array_get_borrowed(v___x_2221_, v_fs_2201_, v_val_2220_);
lean_dec(v_val_2220_);
lean_inc(v_a_2218_);
v___x_2223_ = lean_array_push(v_x_2204_, v_a_2218_);
lean_inc(v___x_2222_);
v___x_2224_ = l_Lean_mkAppN(v___x_2222_, v___x_2223_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = l_Lean_Meta_mkPProdMk(v___x_2224_, v_a_2218_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2225_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v___x_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_x_2204_);
v___x_2226_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2227_ = l_Lean_MessageData_ofExpr(v_minor__type_2202_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = lean_array_to_list(v_motives_2200_);
v___x_2232_ = lean_box(0);
v___x_2233_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2231_, v___x_2232_);
v___x_2234_ = l_Lean_MessageData_ofList(v___x_2233_);
v___x_2235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2230_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2235_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2236_;
}
}
else
{
lean_dec_ref(v_x_2204_);
lean_dec_ref(v_x_2203_);
lean_dec_ref(v_minor__type_2202_);
lean_dec_ref(v_motives_2200_);
return v___x_2217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2237_, lean_object* v_prods_2238_, lean_object* v_motives_2239_, lean_object* v_fs_2240_, lean_object* v_minor__type_2241_, lean_object* v_x_2242_, lean_object* v_x_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2237_, v_prods_2238_, v_motives_2239_, v_fs_2240_, v_minor__type_2241_, v_x_2242_, v_x_2243_, v_x_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec_ref(v_fs_2240_);
return v_res_2250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2251_; lean_object* v_dummy_2252_; 
v___x_2251_ = lean_box(0);
v_dummy_2252_ = l_Lean_Expr_sort___override(v___x_2251_);
return v_dummy_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2253_, lean_object* v_head_2254_, lean_object* v_belows_2255_, lean_object* v_prods_2256_, lean_object* v_rlvl_2257_, lean_object* v_fs_2258_, lean_object* v_minor__type_2259_, lean_object* v_tail_2260_, lean_object* v_arg__args_2261_, lean_object* v_arg__type_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2253_, v_head_2254_, v_belows_2255_, v_prods_2256_, v_rlvl_2257_, v_fs_2258_, v_minor__type_2259_, v_tail_2260_, v_arg__args_2261_, v_arg__type_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_arg__args_2261_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2269_, lean_object* v_motives_2270_, lean_object* v_belows_2271_, lean_object* v_fs_2272_, lean_object* v_minor__type_2273_, lean_object* v_prods_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
if (lean_obj_tag(v_a_2275_) == 0)
{
lean_object* v_dummy_2281_; lean_object* v_nargs_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
lean_dec_ref(v_belows_2271_);
v_dummy_2281_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2282_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2273_);
lean_inc(v_nargs_2282_);
v___x_2283_ = lean_mk_array(v_nargs_2282_, v_dummy_2281_);
v___x_2284_ = lean_unsigned_to_nat(1u);
v___x_2285_ = lean_nat_sub(v_nargs_2282_, v___x_2284_);
lean_dec(v_nargs_2282_);
lean_inc_ref(v_minor__type_2273_);
v___x_2286_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2269_, v_prods_2274_, v_motives_2270_, v_fs_2272_, v_minor__type_2273_, v_minor__type_2273_, v___x_2283_, v___x_2285_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_fs_2272_);
return v___x_2286_;
}
else
{
lean_object* v_head_2287_; lean_object* v_tail_2288_; lean_object* v___x_2289_; 
v_head_2287_ = lean_ctor_get(v_a_2275_, 0);
lean_inc_n(v_head_2287_, 2);
v_tail_2288_ = lean_ctor_get(v_a_2275_, 1);
lean_inc(v_tail_2288_);
lean_dec_ref_known(v_a_2275_, 2);
lean_inc(v_a_2279_);
lean_inc_ref(v_a_2278_);
lean_inc(v_a_2277_);
lean_inc_ref(v_a_2276_);
v___x_2289_ = lean_infer_type(v_head_2287_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___f_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___f_2291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2291_, 0, v_motives_2270_);
lean_closure_set(v___f_2291_, 1, v_head_2287_);
lean_closure_set(v___f_2291_, 2, v_belows_2271_);
lean_closure_set(v___f_2291_, 3, v_prods_2274_);
lean_closure_set(v___f_2291_, 4, v_rlvl_2269_);
lean_closure_set(v___f_2291_, 5, v_fs_2272_);
lean_closure_set(v___f_2291_, 6, v_minor__type_2273_);
lean_closure_set(v___f_2291_, 7, v_tail_2288_);
v___x_2292_ = 0;
v___x_2293_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2290_, v___f_2291_, v___x_2292_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2293_;
}
else
{
lean_dec(v_tail_2288_);
lean_dec(v_head_2287_);
lean_dec_ref(v_prods_2274_);
lean_dec_ref(v_minor__type_2273_);
lean_dec_ref(v_fs_2272_);
lean_dec_ref(v_belows_2271_);
lean_dec_ref(v_motives_2270_);
lean_dec(v_rlvl_2269_);
return v___x_2289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2294_, lean_object* v_rlvl_2295_, lean_object* v_motives_2296_, lean_object* v_belows_2297_, lean_object* v_fs_2298_, lean_object* v_minor__type_2299_, lean_object* v_tail_2300_, uint8_t v___x_2301_, uint8_t v___x_2302_, uint8_t v___x_2303_, lean_object* v_arg_x27_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
lean_inc_ref(v_arg_x27_2304_);
v___x_2310_ = lean_array_push(v_prods_2294_, v_arg_x27_2304_);
v___x_2311_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2295_, v_motives_2296_, v_belows_2297_, v_fs_2298_, v_minor__type_2299_, v___x_2310_, v_tail_2300_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_mk_empty_array_with_capacity(v___x_2313_);
v___x_2315_ = lean_array_push(v___x_2314_, v_arg_x27_2304_);
v___x_2316_ = l_Lean_Meta_mkLambdaFVars(v___x_2315_, v_a_2312_, v___x_2301_, v___x_2302_, v___x_2301_, v___x_2302_, v___x_2303_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec_ref(v___x_2315_);
return v___x_2316_;
}
else
{
lean_dec_ref(v_arg_x27_2304_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2317_, lean_object* v_rlvl_2318_, lean_object* v_motives_2319_, lean_object* v_belows_2320_, lean_object* v_fs_2321_, lean_object* v_minor__type_2322_, lean_object* v_tail_2323_, lean_object* v___x_2324_, lean_object* v___x_2325_, lean_object* v___x_2326_, lean_object* v_arg_x27_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v___x_1774__boxed_2333_; uint8_t v___x_1775__boxed_2334_; uint8_t v___x_1776__boxed_2335_; lean_object* v_res_2336_; 
v___x_1774__boxed_2333_ = lean_unbox(v___x_2324_);
v___x_1775__boxed_2334_ = lean_unbox(v___x_2325_);
v___x_1776__boxed_2335_ = lean_unbox(v___x_2326_);
v_res_2336_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2317_, v_rlvl_2318_, v_motives_2319_, v_belows_2320_, v_fs_2321_, v_minor__type_2322_, v_tail_2323_, v___x_1774__boxed_2333_, v___x_1775__boxed_2334_, v___x_1776__boxed_2335_, v_arg_x27_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2337_, lean_object* v_head_2338_, lean_object* v_belows_2339_, lean_object* v_arg__type_2340_, lean_object* v_prods_2341_, lean_object* v_rlvl_2342_, lean_object* v_fs_2343_, lean_object* v_minor__type_2344_, lean_object* v_tail_2345_, lean_object* v_arg__args_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 5)
{
lean_object* v_fn_2355_; lean_object* v_arg_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_fn_2355_ = lean_ctor_get(v_x_2347_, 0);
lean_inc_ref(v_fn_2355_);
v_arg_2356_ = lean_ctor_get(v_x_2347_, 1);
lean_inc_ref(v_arg_2356_);
lean_dec_ref_known(v_x_2347_, 2);
v___x_2357_ = lean_array_set(v_x_2348_, v_x_2349_, v_arg_2356_);
v___x_2358_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_sub(v_x_2349_, v___x_2358_);
lean_dec(v_x_2349_);
v_x_2347_ = v_fn_2355_;
v_x_2348_ = v___x_2357_;
v_x_2349_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v___x_2361_; 
lean_dec(v_x_2349_);
v___x_2361_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2337_, v_x_2347_);
lean_dec_ref(v_x_2347_);
if (lean_obj_tag(v___x_2361_) == 1)
{
lean_object* v_val_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_val_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Expr_fvarId_x21(v_head_2338_);
lean_dec_ref(v_head_2338_);
v___x_2364_ = l_Lean_FVarId_getUserName___redArg(v___x_2363_, v___y_2350_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v___x_2366_ = l_Lean_instInhabitedExpr;
v___x_2367_ = lean_array_get_borrowed(v___x_2366_, v_belows_2339_, v_val_2362_);
lean_dec(v_val_2362_);
lean_inc(v___x_2367_);
v___x_2368_ = l_Lean_mkAppN(v___x_2367_, v_x_2348_);
lean_dec_ref(v_x_2348_);
v___x_2369_ = l_Lean_Meta_mkPProd(v_arg__type_2340_, v___x_2368_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; uint8_t v___x_2371_; uint8_t v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = 0;
v___x_2372_ = 1;
v___x_2373_ = 1;
v___x_2374_ = l_Lean_Meta_mkForallFVars(v_arg__args_2346_, v_a_2370_, v___x_2371_, v___x_2372_, v___x_2372_, v___x_2373_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v_a_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___f_2379_; lean_object* v___x_2380_; 
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_a_2375_);
lean_dec_ref_known(v___x_2374_, 1);
v___x_2376_ = lean_box(v___x_2371_);
v___x_2377_ = lean_box(v___x_2372_);
v___x_2378_ = lean_box(v___x_2373_);
v___f_2379_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2379_, 0, v_prods_2341_);
lean_closure_set(v___f_2379_, 1, v_rlvl_2342_);
lean_closure_set(v___f_2379_, 2, v_motives_2337_);
lean_closure_set(v___f_2379_, 3, v_belows_2339_);
lean_closure_set(v___f_2379_, 4, v_fs_2343_);
lean_closure_set(v___f_2379_, 5, v_minor__type_2344_);
lean_closure_set(v___f_2379_, 6, v_tail_2345_);
lean_closure_set(v___f_2379_, 7, v___x_2376_);
lean_closure_set(v___f_2379_, 8, v___x_2377_);
lean_closure_set(v___f_2379_, 9, v___x_2378_);
v___x_2380_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2365_, v_a_2375_, v___f_2379_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
return v___x_2380_;
}
else
{
lean_dec(v_a_2365_);
lean_dec(v_tail_2345_);
lean_dec_ref(v_minor__type_2344_);
lean_dec_ref(v_fs_2343_);
lean_dec(v_rlvl_2342_);
lean_dec_ref(v_prods_2341_);
lean_dec_ref(v_belows_2339_);
lean_dec_ref(v_motives_2337_);
return v___x_2374_;
}
}
else
{
lean_dec(v_a_2365_);
lean_dec(v_tail_2345_);
lean_dec_ref(v_minor__type_2344_);
lean_dec_ref(v_fs_2343_);
lean_dec(v_rlvl_2342_);
lean_dec_ref(v_prods_2341_);
lean_dec_ref(v_belows_2339_);
lean_dec_ref(v_motives_2337_);
return v___x_2369_;
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_val_2362_);
lean_dec_ref(v_x_2348_);
lean_dec(v_tail_2345_);
lean_dec_ref(v_minor__type_2344_);
lean_dec_ref(v_fs_2343_);
lean_dec(v_rlvl_2342_);
lean_dec_ref(v_prods_2341_);
lean_dec_ref(v_arg__type_2340_);
lean_dec_ref(v_belows_2339_);
lean_dec_ref(v_motives_2337_);
v_a_2381_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2364_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2364_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v___x_2389_; 
lean_dec(v___x_2361_);
lean_dec_ref(v_x_2348_);
lean_dec_ref(v_arg__type_2340_);
v___x_2389_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2342_, v_motives_2337_, v_belows_2339_, v_fs_2343_, v_minor__type_2344_, v_prods_2341_, v_tail_2345_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; uint8_t v___x_2394_; uint8_t v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = lean_unsigned_to_nat(1u);
v___x_2392_ = lean_mk_empty_array_with_capacity(v___x_2391_);
v___x_2393_ = lean_array_push(v___x_2392_, v_head_2338_);
v___x_2394_ = 0;
v___x_2395_ = 1;
v___x_2396_ = 1;
v___x_2397_ = l_Lean_Meta_mkLambdaFVars(v___x_2393_, v_a_2390_, v___x_2394_, v___x_2395_, v___x_2394_, v___x_2395_, v___x_2396_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec_ref(v___x_2393_);
return v___x_2397_;
}
else
{
lean_dec_ref(v_head_2338_);
return v___x_2389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2398_, lean_object* v_head_2399_, lean_object* v_belows_2400_, lean_object* v_prods_2401_, lean_object* v_rlvl_2402_, lean_object* v_fs_2403_, lean_object* v_minor__type_2404_, lean_object* v_tail_2405_, lean_object* v_arg__args_2406_, lean_object* v_arg__type_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_dummy_2413_; lean_object* v_nargs_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_dummy_2413_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2414_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2407_);
lean_inc(v_nargs_2414_);
v___x_2415_ = lean_mk_array(v_nargs_2414_, v_dummy_2413_);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_nat_sub(v_nargs_2414_, v___x_2416_);
lean_dec(v_nargs_2414_);
lean_inc_ref(v_arg__type_2407_);
v___x_2418_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2398_, v_head_2399_, v_belows_2400_, v_arg__type_2407_, v_prods_2401_, v_rlvl_2402_, v_fs_2403_, v_minor__type_2404_, v_tail_2405_, v_arg__args_2406_, v_arg__type_2407_, v___x_2415_, v___x_2417_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2419_, lean_object* v_motives_2420_, lean_object* v_belows_2421_, lean_object* v_fs_2422_, lean_object* v_minor__type_2423_, lean_object* v_prods_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2419_, v_motives_2420_, v_belows_2421_, v_fs_2422_, v_minor__type_2423_, v_prods_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2432_ = _args[0];
lean_object* v_head_2433_ = _args[1];
lean_object* v_belows_2434_ = _args[2];
lean_object* v_arg__type_2435_ = _args[3];
lean_object* v_prods_2436_ = _args[4];
lean_object* v_rlvl_2437_ = _args[5];
lean_object* v_fs_2438_ = _args[6];
lean_object* v_minor__type_2439_ = _args[7];
lean_object* v_tail_2440_ = _args[8];
lean_object* v_arg__args_2441_ = _args[9];
lean_object* v_x_2442_ = _args[10];
lean_object* v_x_2443_ = _args[11];
lean_object* v_x_2444_ = _args[12];
lean_object* v___y_2445_ = _args[13];
lean_object* v___y_2446_ = _args[14];
lean_object* v___y_2447_ = _args[15];
lean_object* v___y_2448_ = _args[16];
lean_object* v___y_2449_ = _args[17];
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2432_, v_head_2433_, v_belows_2434_, v_arg__type_2435_, v_prods_2436_, v_rlvl_2437_, v_fs_2438_, v_minor__type_2439_, v_tail_2440_, v_arg__args_2441_, v_x_2442_, v_x_2443_, v_x_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v_arg__args_2441_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2451_, lean_object* v_motives_2452_, lean_object* v_belows_2453_, lean_object* v_fs_2454_, lean_object* v_minor__args_2455_, lean_object* v_minor__type_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2463_ = lean_array_to_list(v_minor__args_2455_);
v___x_2464_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2451_, v_motives_2452_, v_belows_2453_, v_fs_2454_, v_minor__type_2456_, v___x_2462_, v___x_2463_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2465_, lean_object* v_motives_2466_, lean_object* v_belows_2467_, lean_object* v_fs_2468_, lean_object* v_minor__args_2469_, lean_object* v_minor__type_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2465_, v_motives_2466_, v_belows_2467_, v_fs_2468_, v_minor__args_2469_, v_minor__type_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2477_, lean_object* v_motives_2478_, lean_object* v_belows_2479_, lean_object* v_fs_2480_, lean_object* v_minorType_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v___f_2487_; uint8_t v___x_2488_; lean_object* v___x_2489_; 
v___f_2487_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2487_, 0, v_rlvl_2477_);
lean_closure_set(v___f_2487_, 1, v_motives_2478_);
lean_closure_set(v___f_2487_, 2, v_belows_2479_);
lean_closure_set(v___f_2487_, 3, v_fs_2480_);
v___x_2488_ = 0;
v___x_2489_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2481_, v___f_2487_, v___x_2488_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2490_, lean_object* v_motives_2491_, lean_object* v_belows_2492_, lean_object* v_fs_2493_, lean_object* v_minorType_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2490_, v_motives_2491_, v_belows_2492_, v_fs_2493_, v_minorType_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___f_2507_; lean_object* v___x_27349__overap_2508_; lean_object* v___x_2509_; 
v___f_2507_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27349__overap_2508_ = lean_panic_fn_borrowed(v___f_2507_, v_msg_2501_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
v___x_2509_ = lean_apply_5(v___x_27349__overap_2508_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, lean_box(0));
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = l_Lean_Expr_hasMVar(v_e_2517_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v_e_2517_);
return v___x_2521_;
}
else
{
lean_object* v___x_2522_; lean_object* v_mctx_2523_; lean_object* v___x_2524_; lean_object* v_fst_2525_; lean_object* v_snd_2526_; lean_object* v___x_2527_; lean_object* v_cache_2528_; lean_object* v_zetaDeltaFVarIds_2529_; lean_object* v_postponed_2530_; lean_object* v_diag_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2540_; 
v___x_2522_ = lean_st_ref_get(v___y_2518_);
v_mctx_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc_ref(v_mctx_2523_);
lean_dec(v___x_2522_);
v___x_2524_ = l_Lean_instantiateMVarsCore(v_mctx_2523_, v_e_2517_);
v_fst_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_fst_2525_);
v_snd_2526_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v___x_2524_);
v___x_2527_ = lean_st_ref_take(v___y_2518_);
v_cache_2528_ = lean_ctor_get(v___x_2527_, 1);
v_zetaDeltaFVarIds_2529_ = lean_ctor_get(v___x_2527_, 2);
v_postponed_2530_ = lean_ctor_get(v___x_2527_, 3);
v_diag_2531_ = lean_ctor_get(v___x_2527_, 4);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2527_, 0);
lean_dec(v_unused_2541_);
v___x_2533_ = v___x_2527_;
v_isShared_2534_ = v_isSharedCheck_2540_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_diag_2531_);
lean_inc(v_postponed_2530_);
lean_inc(v_zetaDeltaFVarIds_2529_);
lean_inc(v_cache_2528_);
lean_dec(v___x_2527_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2540_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v_snd_2526_);
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_snd_2526_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_cache_2528_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_zetaDeltaFVarIds_2529_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_postponed_2530_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_diag_2531_);
v___x_2536_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_st_ref_set(v___y_2518_, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_fst_2525_);
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2542_, v___y_2543_);
lean_dec(v___y_2543_);
return v_res_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2546_, v___y_2548_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; lean_object* v_env_2564_; lean_object* v_toConstantVal_2565_; lean_object* v_value_2566_; lean_object* v_all_2567_; uint8_t v___y_2569_; lean_object* v_type_2577_; uint8_t v___x_2578_; 
v___x_2563_ = lean_st_ref_get(v___y_2561_);
v_env_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_ref_n(v_env_2564_, 2);
lean_dec(v___x_2563_);
v_toConstantVal_2565_ = lean_ctor_get(v_thm_2560_, 0);
v_value_2566_ = lean_ctor_get(v_thm_2560_, 1);
v_all_2567_ = lean_ctor_get(v_thm_2560_, 2);
v_type_2577_ = lean_ctor_get(v_toConstantVal_2565_, 2);
v___x_2578_ = l_Lean_Environment_hasUnsafe(v_env_2564_, v_type_2577_);
if (v___x_2578_ == 0)
{
uint8_t v___x_2579_; 
v___x_2579_ = l_Lean_Environment_hasUnsafe(v_env_2564_, v_value_2566_);
v___y_2569_ = v___x_2579_;
goto v___jp_2568_;
}
else
{
lean_dec_ref(v_env_2564_);
v___y_2569_ = v___x_2578_;
goto v___jp_2568_;
}
v___jp_2568_:
{
if (v___y_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2570_, 0, v_thm_2560_);
v___x_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
lean_inc(v_all_2567_);
lean_inc_ref(v_value_2566_);
lean_inc_ref(v_toConstantVal_2565_);
lean_dec_ref(v_thm_2560_);
v___x_2572_ = lean_box(0);
v___x_2573_ = 0;
v___x_2574_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2574_, 0, v_toConstantVal_2565_);
lean_ctor_set(v___x_2574_, 1, v_value_2566_);
lean_ctor_set(v___x_2574_, 2, v___x_2572_);
lean_ctor_set(v___x_2574_, 3, v_all_2567_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*4, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
lean_object* v_res_2583_; 
v_res_2583_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2580_, v___y_2581_);
lean_dec(v___y_2581_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2584_, v___y_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2599_, lean_object* v___x_2600_, lean_object* v___x_2601_, lean_object* v_all_2602_, lean_object* v___x_2603_, lean_object* v___x_2604_, lean_object* v_x_2605_){
_start:
{
lean_object* v___y_2607_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2611_ = lean_array_get_size(v_all_2602_);
v___x_2612_ = lean_nat_dec_lt(v_x_2605_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_array_get_borrowed(v___x_2613_, v_all_2602_, v___x_2603_);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2616_ = lean_nat_sub(v_x_2605_, v___x_2611_);
v___x_2617_ = lean_nat_add(v___x_2616_, v___x_2604_);
lean_dec(v___x_2616_);
v___x_2618_ = l_Nat_reprFast(v___x_2617_);
v___x_2619_ = lean_string_append(v___x_2615_, v___x_2618_);
lean_dec_ref(v___x_2618_);
lean_inc(v___x_2614_);
v___x_2620_ = l_Lean_Name_str___override(v___x_2614_, v___x_2619_);
v___y_2607_ = v___x_2620_;
goto v___jp_2606_;
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_array_fget_borrowed(v_all_2602_, v_x_2605_);
lean_inc(v___x_2621_);
v___x_2622_ = l_Lean_mkBelowName(v___x_2621_);
v___y_2607_ = v___x_2622_;
goto v___jp_2606_;
}
v___jp_2606_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = l_Lean_Expr_const___override(v___y_2607_, v___x_2599_);
v___x_2609_ = l_Array_append___redArg(v___x_2600_, v___x_2601_);
v___x_2610_ = l_Lean_mkAppN(v___x_2608_, v___x_2609_);
lean_dec_ref(v___x_2609_);
return v___x_2610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2623_, lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v_all_2626_, lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v_x_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2623_, v___x_2624_, v___x_2625_, v_all_2626_, v___x_2627_, v___x_2628_, v_x_2629_);
lean_dec(v_x_2629_);
lean_dec(v___x_2628_);
lean_dec(v___x_2627_);
lean_dec_ref(v_all_2626_);
lean_dec_ref(v___x_2625_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2631_, lean_object* v___x_2632_, uint8_t v___x_2633_, lean_object* v_targs_2634_, lean_object* v_x_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = l_Lean_mkAppN(v_a_2631_, v_targs_2634_);
v___x_2642_ = l_Lean_mkAppN(v___x_2632_, v_targs_2634_);
v___x_2643_ = l_Lean_Meta_mkPProd(v___x_2641_, v___x_2642_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; uint8_t v___x_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = 0;
v___x_2646_ = 1;
v___x_2647_ = l_Lean_Meta_mkLambdaFVars(v_targs_2634_, v_a_2644_, v___x_2645_, v___x_2633_, v___x_2645_, v___x_2633_, v___x_2646_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2647_;
}
else
{
return v___x_2643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_targs_2651_, lean_object* v_x_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
uint8_t v___x_30511__boxed_2658_; lean_object* v_res_2659_; 
v___x_30511__boxed_2658_ = lean_unbox(v___x_2650_);
v_res_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2648_, v___x_2649_, v___x_30511__boxed_2658_, v_targs_2651_, v_x_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_x_2652_);
lean_dec_ref(v_targs_2651_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v_as_2660_, size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_usize_dec_lt(v_i_2662_, v_sz_2661_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_b_2663_);
return v___x_2670_;
}
else
{
lean_object* v_snd_2671_; lean_object* v_fst_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2728_; 
v_snd_2671_ = lean_ctor_get(v_b_2663_, 1);
v_fst_2672_ = lean_ctor_get(v_b_2663_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2674_ = v_b_2663_;
v_isShared_2675_ = v_isSharedCheck_2728_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_snd_2671_);
lean_inc(v_fst_2672_);
lean_dec(v_b_2663_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2728_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_array_2676_; lean_object* v_start_2677_; lean_object* v_stop_2678_; uint8_t v___x_2679_; 
v_array_2676_ = lean_ctor_get(v_snd_2671_, 0);
v_start_2677_ = lean_ctor_get(v_snd_2671_, 1);
v_stop_2678_ = lean_ctor_get(v_snd_2671_, 2);
v___x_2679_ = lean_nat_dec_lt(v_start_2677_, v_stop_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2681_; 
if (v_isShared_2675_ == 0)
{
v___x_2681_ = v___x_2674_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_fst_2672_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_snd_2671_);
v___x_2681_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
return v___x_2682_;
}
}
else
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2724_; 
lean_inc(v_stop_2678_);
lean_inc(v_start_2677_);
lean_inc_ref(v_array_2676_);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_snd_2671_);
if (v_isSharedCheck_2724_ == 0)
{
lean_object* v_unused_2725_; lean_object* v_unused_2726_; lean_object* v_unused_2727_; 
v_unused_2725_ = lean_ctor_get(v_snd_2671_, 2);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_snd_2671_, 1);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_snd_2671_, 0);
lean_dec(v_unused_2727_);
v___x_2685_ = v_snd_2671_;
v_isShared_2686_ = v_isSharedCheck_2724_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_snd_2671_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2724_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v_a_2687_; lean_object* v___x_2688_; 
v_a_2687_ = lean_array_uget_borrowed(v_as_2660_, v_i_2662_);
lean_inc(v___y_2667_);
lean_inc_ref(v___y_2666_);
lean_inc(v___y_2665_);
lean_inc_ref(v___y_2664_);
lean_inc(v_a_2687_);
v___x_2688_ = lean_infer_type(v_a_2687_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = lean_array_fget_borrowed(v_array_2676_, v_start_2677_);
v___x_2691_ = lean_box(v___x_2679_);
lean_inc(v___x_2690_);
lean_inc(v_a_2687_);
v___f_2692_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2692_, 0, v_a_2687_);
lean_closure_set(v___f_2692_, 1, v___x_2690_);
lean_closure_set(v___f_2692_, 2, v___x_2691_);
v___x_2693_ = 0;
v___x_2694_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2689_, v___f_2692_, v___x_2693_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_start_2677_, v___x_2696_);
lean_dec(v_start_2677_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2697_);
v___x_2699_ = v___x_2685_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_array_2676_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_stop_2678_);
v___x_2699_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2700_ = l_Lean_Expr_app___override(v_fst_2672_, v_a_2695_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___x_2699_);
lean_ctor_set(v___x_2674_, 0, v___x_2700_);
v___x_2702_ = v___x_2674_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___x_2699_);
v___x_2702_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
size_t v___x_2703_; size_t v___x_2704_; 
v___x_2703_ = ((size_t)1ULL);
v___x_2704_ = lean_usize_add(v_i_2662_, v___x_2703_);
v_i_2662_ = v___x_2704_;
v_b_2663_ = v___x_2702_;
goto _start;
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_del_object(v___x_2685_);
lean_dec(v_stop_2678_);
lean_dec(v_start_2677_);
lean_dec_ref(v_array_2676_);
lean_del_object(v___x_2674_);
lean_dec(v_fst_2672_);
v_a_2708_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2694_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2694_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2685_);
lean_dec(v_stop_2678_);
lean_dec(v_start_2677_);
lean_dec_ref(v_array_2676_);
lean_del_object(v___x_2674_);
lean_dec(v_fst_2672_);
v_a_2716_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2688_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2688_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v_as_2729_, lean_object* v_sz_2730_, lean_object* v_i_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2730_);
lean_dec(v_sz_2730_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v_as_2729_, v_sz_boxed_2738_, v_i_boxed_2739_, v_b_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_as_2729_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2741_, size_t v_sz_2742_, size_t v_i_2743_, lean_object* v_b_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_lt(v_i_2743_, v_sz_2742_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_b_2744_);
return v___x_2751_;
}
else
{
lean_object* v_a_2752_; lean_object* v_toInductionSubgoal_2753_; lean_object* v_mvarId_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2752_ = lean_array_uget_borrowed(v_as_2741_, v_i_2743_);
v_toInductionSubgoal_2753_ = lean_ctor_get(v_a_2752_, 0);
v_mvarId_2754_ = lean_ctor_get(v_toInductionSubgoal_2753_, 0);
v___x_2755_ = 0;
lean_inc(v_mvarId_2754_);
v___x_2756_ = l_Lean_MVarId_refl(v_mvarId_2754_, v___x_2755_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v___x_2757_; size_t v___x_2758_; size_t v___x_2759_; 
lean_dec_ref_known(v___x_2756_, 1);
v___x_2757_ = lean_box(0);
v___x_2758_ = ((size_t)1ULL);
v___x_2759_ = lean_usize_add(v_i_2743_, v___x_2758_);
v_i_2743_ = v___x_2759_;
v_b_2744_ = v___x_2757_;
goto _start;
}
else
{
return v___x_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2761_, lean_object* v_sz_2762_, lean_object* v_i_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
size_t v_sz_boxed_2770_; size_t v_i_boxed_2771_; lean_object* v_res_2772_; 
v_sz_boxed_2770_ = lean_unbox_usize(v_sz_2762_);
lean_dec(v_sz_2762_);
v_i_boxed_2771_ = lean_unbox_usize(v_i_2763_);
lean_dec(v_i_2763_);
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2761_, v_sz_boxed_2770_, v_i_boxed_2771_, v_b_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec_ref(v_as_2761_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2773_, lean_object* v___x_2774_, lean_object* v___x_2775_, lean_object* v_fs_2776_, lean_object* v_as_2777_, size_t v_sz_2778_, size_t v_i_2779_, lean_object* v_b_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = lean_usize_dec_lt(v_i_2779_, v_sz_2778_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
lean_dec_ref(v_fs_2776_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v___x_2774_);
lean_dec(v___x_2773_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_b_2780_);
return v___x_2787_;
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_array_uget_borrowed(v_as_2777_, v_i_2779_);
lean_inc(v___y_2784_);
lean_inc_ref(v___y_2783_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v_a_2788_);
v___x_2789_ = lean_infer_type(v_a_2788_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
lean_inc_ref(v_fs_2776_);
lean_inc_ref(v___x_2775_);
lean_inc_ref(v___x_2774_);
lean_inc(v___x_2773_);
v___x_2791_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2773_, v___x_2774_, v___x_2775_, v_fs_2776_, v_a_2790_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_Expr_app___override(v_b_2780_, v_a_2792_);
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = lean_usize_add(v_i_2779_, v___x_2794_);
v_i_2779_ = v___x_2795_;
v_b_2780_ = v___x_2793_;
goto _start;
}
else
{
lean_dec_ref(v_b_2780_);
lean_dec_ref(v_fs_2776_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v___x_2774_);
lean_dec(v___x_2773_);
return v___x_2791_;
}
}
else
{
lean_dec_ref(v_b_2780_);
lean_dec_ref(v_fs_2776_);
lean_dec_ref(v___x_2775_);
lean_dec_ref(v___x_2774_);
lean_dec(v___x_2773_);
return v___x_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v___x_2799_, lean_object* v_fs_2800_, lean_object* v_as_2801_, lean_object* v_sz_2802_, lean_object* v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
size_t v_sz_boxed_2810_; size_t v_i_boxed_2811_; lean_object* v_res_2812_; 
v_sz_boxed_2810_ = lean_unbox_usize(v_sz_2802_);
lean_dec(v_sz_2802_);
v_i_boxed_2811_ = lean_unbox_usize(v_i_2803_);
lean_dec(v_i_2803_);
v_res_2812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2797_, v___x_2798_, v___x_2799_, v_fs_2800_, v_as_2801_, v_sz_boxed_2810_, v_i_boxed_2811_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v_as_2801_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2813_, lean_object* v_tail_2814_, lean_object* v_recName_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, size_t v_sz_2819_, size_t v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_val_2827_, uint8_t v___x_2828_, lean_object* v_brecOnGoName_2829_, lean_object* v_levelParams_2830_, lean_object* v___x_2831_, lean_object* v_brecOnName_2832_, lean_object* v___x_2833_, lean_object* v_brecOnEqName_2834_, lean_object* v_fs_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_inc(v___x_2813_);
v___x_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2813_);
lean_ctor_set(v___x_2841_, 1, v_tail_2814_);
v___x_2842_ = l_Lean_Expr_const___override(v_recName_2815_, v___x_2841_);
v___x_2843_ = l_Lean_mkAppN(v___x_2842_, v___x_2816_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___x_2817_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2818_, v_sz_2819_, v___x_2820_, v___x_2844_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v_fst_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_3208_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v_fst_2847_ = lean_ctor_get(v_a_2846_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_a_2846_);
if (v_isSharedCheck_3208_ == 0)
{
lean_object* v_unused_3209_; 
v_unused_3209_ = lean_ctor_get(v_a_2846_, 1);
lean_dec(v_unused_3209_);
v___x_2849_ = v_a_2846_;
v_isShared_2850_ = v_isSharedCheck_3208_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_fst_2847_);
lean_dec(v_a_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_3208_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
size_t v_sz_2851_; lean_object* v___x_2852_; 
v_sz_2851_ = lean_array_size(v___x_2821_);
lean_inc_ref(v_fs_2835_);
lean_inc_ref(v___x_2822_);
lean_inc_ref(v___x_2818_);
v___x_2852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2813_, v___x_2818_, v___x_2822_, v_fs_2835_, v___x_2821_, v_sz_2851_, v___x_2820_, v_fst_2847_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v___x_2854_ = l_Lean_mkAppN(v_a_2853_, v___x_2823_);
lean_inc_ref_n(v___x_2824_, 3);
v___x_2855_ = l_Lean_Expr_app___override(v___x_2854_, v___x_2824_);
v___x_2856_ = l_Array_append___redArg(v___x_2816_, v___x_2818_);
v___x_2857_ = l_Array_append___redArg(v___x_2856_, v___x_2823_);
v___x_2858_ = lean_mk_empty_array_with_capacity(v___x_2825_);
v___x_2859_ = lean_array_push(v___x_2858_, v___x_2824_);
v___x_2860_ = lean_array_get(v___x_2826_, v___x_2818_, v_val_2827_);
lean_dec_ref(v___x_2818_);
v___x_2861_ = lean_array_push(v___x_2823_, v___x_2824_);
v___x_2862_ = l_Lean_mkAppN(v___x_2860_, v___x_2861_);
v___x_2863_ = lean_array_get(v___x_2826_, v___x_2822_, v_val_2827_);
lean_dec_ref(v___x_2822_);
v___x_2864_ = l_Lean_mkAppN(v___x_2863_, v___x_2861_);
lean_inc_ref(v___x_2862_);
v___x_2865_ = l_Lean_Meta_mkPProd(v___x_2862_, v___x_2864_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = l_Array_append___redArg(v___x_2857_, v___x_2859_);
lean_dec_ref(v___x_2859_);
v___x_2868_ = l_Array_append___redArg(v___x_2867_, v_fs_2835_);
v___x_2869_ = 0;
v___x_2870_ = 1;
v___x_2871_ = l_Lean_Meta_mkForallFVars(v___x_2868_, v_a_2866_, v___x_2869_, v___x_2828_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_Meta_mkLambdaFVars(v___x_2868_, v___x_2855_, v___x_2869_, v___x_2828_, v___x_2869_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_3175_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = lean_box(1);
lean_inc(v_levelParams_2830_);
lean_inc(v_brecOnGoName_2829_);
v___x_2876_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2829_, v_levelParams_2830_, v_a_2872_, v_a_2874_, v___x_2875_, v___y_2839_);
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_2879_ = v___x_2876_;
v_isShared_2880_ = v_isSharedCheck_3175_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_3175_;
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
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_3174_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_addDecl(v___x_2882_, v___x_2869_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_toConstantVal_2884_; lean_object* v_name_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref_known(v___x_2883_, 1);
v_toConstantVal_2884_ = lean_ctor_get(v_a_2877_, 0);
lean_inc_ref(v_toConstantVal_2884_);
lean_dec(v_a_2877_);
v_name_2885_ = lean_ctor_get(v_toConstantVal_2884_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_toConstantVal_2884_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; lean_object* v_unused_3173_; 
v_unused_3172_ = lean_ctor_get(v_toConstantVal_2884_, 2);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_toConstantVal_2884_, 1);
lean_dec(v_unused_3173_);
v___x_2887_ = v_toConstantVal_2884_;
v_isShared_2888_ = v_isSharedCheck_3171_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_name_2885_);
lean_dec(v_toConstantVal_2884_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_3171_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v_nextMacroScope_2892_; lean_object* v_ngen_2893_; lean_object* v_auxDeclNGen_2894_; lean_object* v_traceState_2895_; lean_object* v_messages_2896_; lean_object* v_infoState_2897_; lean_object* v_snapshotTasks_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_3169_; 
lean_inc(v_name_2885_);
v___x_2889_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2885_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2889_);
v___x_2890_ = lean_st_ref_take(v___y_2839_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
v_nextMacroScope_2892_ = lean_ctor_get(v___x_2890_, 1);
v_ngen_2893_ = lean_ctor_get(v___x_2890_, 2);
v_auxDeclNGen_2894_ = lean_ctor_get(v___x_2890_, 3);
v_traceState_2895_ = lean_ctor_get(v___x_2890_, 4);
v_messages_2896_ = lean_ctor_get(v___x_2890_, 6);
v_infoState_2897_ = lean_ctor_get(v___x_2890_, 7);
v_snapshotTasks_2898_ = lean_ctor_get(v___x_2890_, 8);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v___x_2890_, 5);
lean_dec(v_unused_3170_);
v___x_2900_ = v___x_2890_;
v_isShared_2901_ = v_isSharedCheck_3169_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_snapshotTasks_2898_);
lean_inc(v_infoState_2897_);
lean_inc(v_messages_2896_);
lean_inc(v_traceState_2895_);
lean_inc(v_auxDeclNGen_2894_);
lean_inc(v_ngen_2893_);
lean_inc(v_nextMacroScope_2892_);
lean_inc(v_env_2891_);
lean_dec(v___x_2890_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_3169_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2902_ = l_Lean_addProtected(v_env_2891_, v_name_2885_);
v___x_2903_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 5, v___x_2903_);
lean_ctor_set(v___x_2900_, 0, v___x_2902_);
v___x_2905_ = v___x_2900_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_nextMacroScope_2892_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_ngen_2893_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_auxDeclNGen_2894_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v_traceState_2895_);
lean_ctor_set(v_reuseFailAlloc_3168_, 5, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_3168_, 6, v_messages_2896_);
lean_ctor_set(v_reuseFailAlloc_3168_, 7, v_infoState_2897_);
lean_ctor_set(v_reuseFailAlloc_3168_, 8, v_snapshotTasks_2898_);
v___x_2905_ = v_reuseFailAlloc_3168_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v_mctx_2908_; lean_object* v_zetaDeltaFVarIds_2909_; lean_object* v_postponed_2910_; lean_object* v_diag_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3166_; 
v___x_2906_ = lean_st_ref_set(v___y_2839_, v___x_2905_);
v___x_2907_ = lean_st_ref_take(v___y_2837_);
v_mctx_2908_ = lean_ctor_get(v___x_2907_, 0);
v_zetaDeltaFVarIds_2909_ = lean_ctor_get(v___x_2907_, 2);
v_postponed_2910_ = lean_ctor_get(v___x_2907_, 3);
v_diag_2911_ = lean_ctor_get(v___x_2907_, 4);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_2907_, 1);
lean_dec(v_unused_3167_);
v___x_2913_ = v___x_2907_;
v_isShared_2914_ = v_isSharedCheck_3166_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_diag_2911_);
lean_inc(v_postponed_2910_);
lean_inc(v_zetaDeltaFVarIds_2909_);
lean_inc(v_mctx_2908_);
lean_dec(v___x_2907_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3166_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2915_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_mctx_2908_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_zetaDeltaFVarIds_2909_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_postponed_2910_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_diag_2911_);
v___x_2917_ = v_reuseFailAlloc_3165_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2918_ = lean_st_ref_set(v___y_2837_, v___x_2917_);
lean_inc(v___x_2831_);
v___x_2919_ = l_Lean_Expr_const___override(v_brecOnGoName_2829_, v___x_2831_);
v___x_2920_ = l_Lean_mkAppN(v___x_2919_, v___x_2868_);
lean_inc_ref(v___x_2920_);
v___x_2921_ = l_Lean_Meta_mkPProdFstM(v___x_2920_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = l_Lean_Meta_mkLambdaFVars(v___x_2868_, v_a_2922_, v___x_2869_, v___x_2828_, v___x_2869_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_mkForallFVars(v___x_2868_, v___x_2862_, v___x_2869_, v___x_2828_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_3140_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
lean_inc(v_levelParams_2830_);
v___x_2927_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2832_, v_levelParams_2830_, v_a_2926_, v_a_2924_, v___x_2875_, v___y_2839_);
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_3140_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_3140_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
lean_inc(v_a_2928_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set_tag(v___x_2930_, 1);
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_3139_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_addDecl(v___x_2933_, v___x_2869_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_toConstantVal_2935_; lean_object* v_name_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref_known(v___x_2934_, 1);
v_toConstantVal_2935_ = lean_ctor_get(v_a_2928_, 0);
lean_inc_ref(v_toConstantVal_2935_);
lean_dec(v_a_2928_);
v_name_2936_ = lean_ctor_get(v_toConstantVal_2935_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_toConstantVal_2935_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3137_ = lean_ctor_get(v_toConstantVal_2935_, 2);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_toConstantVal_2935_, 1);
lean_dec(v_unused_3138_);
v___x_2938_ = v_toConstantVal_2935_;
v_isShared_2939_ = v_isSharedCheck_3136_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_name_2936_);
lean_dec(v_toConstantVal_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_3136_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v_env_2942_; lean_object* v_nextMacroScope_2943_; lean_object* v_ngen_2944_; lean_object* v_auxDeclNGen_2945_; lean_object* v_traceState_2946_; lean_object* v_messages_2947_; lean_object* v_infoState_2948_; lean_object* v_snapshotTasks_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3134_; 
lean_inc(v_name_2936_);
v___x_2940_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2936_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2940_);
v___x_2941_ = lean_st_ref_take(v___y_2839_);
v_env_2942_ = lean_ctor_get(v___x_2941_, 0);
v_nextMacroScope_2943_ = lean_ctor_get(v___x_2941_, 1);
v_ngen_2944_ = lean_ctor_get(v___x_2941_, 2);
v_auxDeclNGen_2945_ = lean_ctor_get(v___x_2941_, 3);
v_traceState_2946_ = lean_ctor_get(v___x_2941_, 4);
v_messages_2947_ = lean_ctor_get(v___x_2941_, 6);
v_infoState_2948_ = lean_ctor_get(v___x_2941_, 7);
v_snapshotTasks_2949_ = lean_ctor_get(v___x_2941_, 8);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_2941_, 5);
lean_dec(v_unused_3135_);
v___x_2951_ = v___x_2941_;
v_isShared_2952_ = v_isSharedCheck_3134_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_snapshotTasks_2949_);
lean_inc(v_infoState_2948_);
lean_inc(v_messages_2947_);
lean_inc(v_traceState_2946_);
lean_inc(v_auxDeclNGen_2945_);
lean_inc(v_ngen_2944_);
lean_inc(v_nextMacroScope_2943_);
lean_inc(v_env_2942_);
lean_dec(v___x_2941_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3134_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; lean_object* v___x_2955_; 
lean_inc(v_name_2936_);
v___x_2953_ = l_Lean_markAuxRecursor(v_env_2942_, v_name_2936_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 5, v___x_2903_);
lean_ctor_set(v___x_2951_, 0, v___x_2953_);
v___x_2955_ = v___x_2951_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_2953_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_nextMacroScope_2943_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_ngen_2944_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_auxDeclNGen_2945_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v_traceState_2946_);
lean_ctor_set(v_reuseFailAlloc_3133_, 5, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_3133_, 6, v_messages_2947_);
lean_ctor_set(v_reuseFailAlloc_3133_, 7, v_infoState_2948_);
lean_ctor_set(v_reuseFailAlloc_3133_, 8, v_snapshotTasks_2949_);
v___x_2955_ = v_reuseFailAlloc_3133_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v_mctx_2958_; lean_object* v_zetaDeltaFVarIds_2959_; lean_object* v_postponed_2960_; lean_object* v_diag_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3131_; 
v___x_2956_ = lean_st_ref_set(v___y_2839_, v___x_2955_);
v___x_2957_ = lean_st_ref_take(v___y_2837_);
v_mctx_2958_ = lean_ctor_get(v___x_2957_, 0);
v_zetaDeltaFVarIds_2959_ = lean_ctor_get(v___x_2957_, 2);
v_postponed_2960_ = lean_ctor_get(v___x_2957_, 3);
v_diag_2961_ = lean_ctor_get(v___x_2957_, 4);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v___x_2957_, 1);
lean_dec(v_unused_3132_);
v___x_2963_ = v___x_2957_;
v_isShared_2964_ = v_isSharedCheck_3131_;
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
v_isShared_2964_ = v_isSharedCheck_3131_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2915_);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_mctx_2958_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_zetaDeltaFVarIds_2959_);
lean_ctor_set(v_reuseFailAlloc_3130_, 3, v_postponed_2960_);
lean_ctor_set(v_reuseFailAlloc_3130_, 4, v_diag_2961_);
v___x_2966_ = v_reuseFailAlloc_3130_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_env_2969_; lean_object* v_nextMacroScope_2970_; lean_object* v_ngen_2971_; lean_object* v_auxDeclNGen_2972_; lean_object* v_traceState_2973_; lean_object* v_messages_2974_; lean_object* v_infoState_2975_; lean_object* v_snapshotTasks_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3128_; 
v___x_2967_ = lean_st_ref_set(v___y_2837_, v___x_2966_);
v___x_2968_ = lean_st_ref_take(v___y_2839_);
v_env_2969_ = lean_ctor_get(v___x_2968_, 0);
v_nextMacroScope_2970_ = lean_ctor_get(v___x_2968_, 1);
v_ngen_2971_ = lean_ctor_get(v___x_2968_, 2);
v_auxDeclNGen_2972_ = lean_ctor_get(v___x_2968_, 3);
v_traceState_2973_ = lean_ctor_get(v___x_2968_, 4);
v_messages_2974_ = lean_ctor_get(v___x_2968_, 6);
v_infoState_2975_ = lean_ctor_get(v___x_2968_, 7);
v_snapshotTasks_2976_ = lean_ctor_get(v___x_2968_, 8);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; 
v_unused_3129_ = lean_ctor_get(v___x_2968_, 5);
lean_dec(v_unused_3129_);
v___x_2978_ = v___x_2968_;
v_isShared_2979_ = v_isSharedCheck_3128_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snapshotTasks_2976_);
lean_inc(v_infoState_2975_);
lean_inc(v_messages_2974_);
lean_inc(v_traceState_2973_);
lean_inc(v_auxDeclNGen_2972_);
lean_inc(v_ngen_2971_);
lean_inc(v_nextMacroScope_2970_);
lean_inc(v_env_2969_);
lean_dec(v___x_2968_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3128_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
lean_inc(v_name_2936_);
v___x_2980_ = l_Lean_addProtected(v_env_2969_, v_name_2936_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 5, v___x_2903_);
lean_ctor_set(v___x_2978_, 0, v___x_2980_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_nextMacroScope_2970_);
lean_ctor_set(v_reuseFailAlloc_3127_, 2, v_ngen_2971_);
lean_ctor_set(v_reuseFailAlloc_3127_, 3, v_auxDeclNGen_2972_);
lean_ctor_set(v_reuseFailAlloc_3127_, 4, v_traceState_2973_);
lean_ctor_set(v_reuseFailAlloc_3127_, 5, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_3127_, 6, v_messages_2974_);
lean_ctor_set(v_reuseFailAlloc_3127_, 7, v_infoState_2975_);
lean_ctor_set(v_reuseFailAlloc_3127_, 8, v_snapshotTasks_2976_);
v___x_2982_ = v_reuseFailAlloc_3127_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v_mctx_2985_; lean_object* v_zetaDeltaFVarIds_2986_; lean_object* v_postponed_2987_; lean_object* v_diag_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3125_; 
v___x_2983_ = lean_st_ref_set(v___y_2839_, v___x_2982_);
v___x_2984_ = lean_st_ref_take(v___y_2837_);
v_mctx_2985_ = lean_ctor_get(v___x_2984_, 0);
v_zetaDeltaFVarIds_2986_ = lean_ctor_get(v___x_2984_, 2);
v_postponed_2987_ = lean_ctor_get(v___x_2984_, 3);
v_diag_2988_ = lean_ctor_get(v___x_2984_, 4);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_2984_, 1);
lean_dec(v_unused_3126_);
v___x_2990_ = v___x_2984_;
v_isShared_2991_ = v_isSharedCheck_3125_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_diag_2988_);
lean_inc(v_postponed_2987_);
lean_inc(v_zetaDeltaFVarIds_2986_);
lean_inc(v_mctx_2985_);
lean_dec(v___x_2984_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3125_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 1, v___x_2915_);
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_mctx_2985_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_zetaDeltaFVarIds_2986_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_postponed_2987_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_diag_2988_);
v___x_2993_ = v_reuseFailAlloc_3124_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_st_ref_set(v___y_2837_, v___x_2993_);
v___x_2995_ = l_Lean_Meta_mkPProdSndM(v___x_2920_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = l_Lean_Expr_const___override(v_name_2936_, v___x_2831_);
v___x_2998_ = l_Lean_mkAppN(v___x_2997_, v___x_2868_);
v___x_2999_ = lean_array_get(v___x_2826_, v_fs_2835_, v_val_2827_);
lean_dec_ref(v_fs_2835_);
v___x_3000_ = l_Lean_mkAppN(v___x_2999_, v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_3001_ = l_Lean_Expr_app___override(v___x_3000_, v_a_2996_);
v___x_3002_ = l_Lean_Meta_mkEq(v___x_2998_, v___x_3001_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc_n(v_a_3003_, 2);
lean_dec_ref_known(v___x_3002_, 1);
v___x_3004_ = lean_box(0);
v___x_3005_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3003_, v___x_3004_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_Expr_mvarId_x21(v_a_3006_);
v___x_3008_ = l_Lean_Expr_fvarId_x21(v___x_2824_);
lean_dec_ref(v___x_2824_);
v___x_3009_ = lean_mk_empty_array_with_capacity(v___x_2833_);
v___x_3010_ = lean_box(0);
v___x_3011_ = l_Lean_MVarId_cases(v___x_3007_, v___x_3008_, v___x_3009_, v___x_2869_, v___x_3010_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; size_t v_sz_3014_; lean_object* v___x_3015_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_box(0);
v_sz_3014_ = lean_array_size(v_a_3012_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3012_, v_sz_3014_, v___x_2820_, v___x_3013_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v_a_3012_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v___x_3016_; lean_object* v_a_3017_; lean_object* v___x_3018_; 
lean_dec_ref_known(v___x_3015_, 1);
v___x_3016_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3006_, v___y_2837_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = l_Lean_Meta_mkForallFVars(v___x_2868_, v_a_3003_, v___x_2869_, v___x_2828_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_Meta_mkLambdaFVars(v___x_2868_, v_a_3017_, v___x_2869_, v___x_2828_, v___x_2869_, v___x_2828_, v___x_2870_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec_ref(v___x_2868_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
lean_inc(v_brecOnEqName_2834_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 2, v_a_3019_);
lean_ctor_set(v___x_2938_, 1, v_levelParams_2830_);
lean_ctor_set(v___x_2938_, 0, v_brecOnEqName_2834_);
v___x_3023_ = v___x_2938_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_brecOnEqName_2834_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_levelParams_2830_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_a_3019_);
v___x_3023_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = lean_box(0);
lean_inc(v_brecOnEqName_2834_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set_tag(v___x_2849_, 1);
lean_ctor_set(v___x_2849_, 1, v___x_3024_);
lean_ctor_set(v___x_2849_, 0, v_brecOnEqName_2834_);
v___x_3026_ = v___x_2849_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_brecOnEqName_2834_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 2, v___x_3026_);
lean_ctor_set(v___x_2887_, 1, v_a_3021_);
lean_ctor_set(v___x_2887_, 0, v___x_3023_);
v___x_3028_ = v___x_2887_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_a_3021_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v_a_3030_; lean_object* v___x_3031_; 
v___x_3029_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3028_, v___y_2839_);
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref(v___x_3029_);
v___x_3031_ = l_Lean_addDecl(v_a_3030_, v___x_2869_, v___y_2838_, v___y_2839_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3071_; 
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3031_, 0);
lean_dec(v_unused_3072_);
v___x_3033_ = v___x_3031_;
v_isShared_3034_ = v_isSharedCheck_3071_;
goto v_resetjp_3032_;
}
else
{
lean_dec(v___x_3031_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3071_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3035_; lean_object* v_env_3036_; lean_object* v_nextMacroScope_3037_; lean_object* v_ngen_3038_; lean_object* v_auxDeclNGen_3039_; lean_object* v_traceState_3040_; lean_object* v_messages_3041_; lean_object* v_infoState_3042_; lean_object* v_snapshotTasks_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3069_; 
v___x_3035_ = lean_st_ref_take(v___y_2839_);
v_env_3036_ = lean_ctor_get(v___x_3035_, 0);
v_nextMacroScope_3037_ = lean_ctor_get(v___x_3035_, 1);
v_ngen_3038_ = lean_ctor_get(v___x_3035_, 2);
v_auxDeclNGen_3039_ = lean_ctor_get(v___x_3035_, 3);
v_traceState_3040_ = lean_ctor_get(v___x_3035_, 4);
v_messages_3041_ = lean_ctor_get(v___x_3035_, 6);
v_infoState_3042_ = lean_ctor_get(v___x_3035_, 7);
v_snapshotTasks_3043_ = lean_ctor_get(v___x_3035_, 8);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v___x_3035_, 5);
lean_dec(v_unused_3070_);
v___x_3045_ = v___x_3035_;
v_isShared_3046_ = v_isSharedCheck_3069_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_snapshotTasks_3043_);
lean_inc(v_infoState_3042_);
lean_inc(v_messages_3041_);
lean_inc(v_traceState_3040_);
lean_inc(v_auxDeclNGen_3039_);
lean_inc(v_ngen_3038_);
lean_inc(v_nextMacroScope_3037_);
lean_inc(v_env_3036_);
lean_dec(v___x_3035_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3069_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l_Lean_addProtected(v_env_3036_, v_brecOnEqName_2834_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 5, v___x_2903_);
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v_nextMacroScope_3037_);
lean_ctor_set(v_reuseFailAlloc_3068_, 2, v_ngen_3038_);
lean_ctor_set(v_reuseFailAlloc_3068_, 3, v_auxDeclNGen_3039_);
lean_ctor_set(v_reuseFailAlloc_3068_, 4, v_traceState_3040_);
lean_ctor_set(v_reuseFailAlloc_3068_, 5, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_3068_, 6, v_messages_3041_);
lean_ctor_set(v_reuseFailAlloc_3068_, 7, v_infoState_3042_);
lean_ctor_set(v_reuseFailAlloc_3068_, 8, v_snapshotTasks_3043_);
v___x_3049_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v_mctx_3052_; lean_object* v_zetaDeltaFVarIds_3053_; lean_object* v_postponed_3054_; lean_object* v_diag_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3066_; 
v___x_3050_ = lean_st_ref_set(v___y_2839_, v___x_3049_);
v___x_3051_ = lean_st_ref_take(v___y_2837_);
v_mctx_3052_ = lean_ctor_get(v___x_3051_, 0);
v_zetaDeltaFVarIds_3053_ = lean_ctor_get(v___x_3051_, 2);
v_postponed_3054_ = lean_ctor_get(v___x_3051_, 3);
v_diag_3055_ = lean_ctor_get(v___x_3051_, 4);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v___x_3051_, 1);
lean_dec(v_unused_3067_);
v___x_3057_ = v___x_3051_;
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_diag_3055_);
lean_inc(v_postponed_3054_);
lean_inc(v_zetaDeltaFVarIds_3053_);
lean_inc(v_mctx_3052_);
lean_dec(v___x_3051_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3066_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v___x_2915_);
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_mctx_3052_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_zetaDeltaFVarIds_3053_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_postponed_3054_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_diag_3055_);
v___x_3060_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3061_ = lean_st_ref_set(v___y_2837_, v___x_3060_);
if (v_isShared_3034_ == 0)
{
lean_ctor_set(v___x_3033_, 0, v___x_3013_);
v___x_3063_ = v___x_3033_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3013_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
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
return v___x_3031_;
}
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3019_);
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3076_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3020_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3020_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3017_);
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3084_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3018_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3018_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_dec(v_a_3006_);
lean_dec(v_a_3003_);
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
return v___x_3015_;
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_3006_);
lean_dec(v_a_3003_);
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
v_a_3092_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3011_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3011_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_a_3003_);
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3100_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3005_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3005_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_del_object(v___x_2938_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_del_object(v___x_2849_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3108_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3002_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3002_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_del_object(v___x_2938_);
lean_dec(v_name_2936_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3116_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_2995_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_2995_);
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
lean_dec(v_a_2928_);
lean_dec_ref(v___x_2920_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
return v___x_2934_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec(v_a_2924_);
lean_dec_ref(v___x_2920_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3141_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_2925_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_2925_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v___x_2920_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3149_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_2923_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_2923_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v___x_2920_);
lean_del_object(v___x_2887_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec_ref(v___x_2824_);
v_a_3157_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_2921_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_2921_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
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
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_a_2872_);
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3176_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_2873_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_2873_);
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
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v___x_2868_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2855_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3184_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_2871_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_2871_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2861_);
lean_dec_ref(v___x_2859_);
lean_dec_ref(v___x_2857_);
lean_dec_ref(v___x_2855_);
lean_del_object(v___x_2849_);
lean_dec_ref(v_fs_2835_);
lean_dec(v_brecOnEqName_2834_);
lean_dec(v_brecOnName_2832_);
lean_dec(v___x_2831_);
lean_dec(v_levelParams_2830_);
lean_dec(v_brecOnGoName_2829_);
lean_dec_ref(v___x_2824_);
v_a_3192_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_2865_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_2865_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_2849_);
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
v_a_3200_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_2852_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_2852_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
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
v_a_3210_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_2845_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_2845_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3218_ = _args[0];
lean_object* v_tail_3219_ = _args[1];
lean_object* v_recName_3220_ = _args[2];
lean_object* v___x_3221_ = _args[3];
lean_object* v___x_3222_ = _args[4];
lean_object* v___x_3223_ = _args[5];
lean_object* v_sz_3224_ = _args[6];
lean_object* v___x_3225_ = _args[7];
lean_object* v___x_3226_ = _args[8];
lean_object* v___x_3227_ = _args[9];
lean_object* v___x_3228_ = _args[10];
lean_object* v___x_3229_ = _args[11];
lean_object* v___x_3230_ = _args[12];
lean_object* v___x_3231_ = _args[13];
lean_object* v_val_3232_ = _args[14];
lean_object* v___x_3233_ = _args[15];
lean_object* v_brecOnGoName_3234_ = _args[16];
lean_object* v_levelParams_3235_ = _args[17];
lean_object* v___x_3236_ = _args[18];
lean_object* v_brecOnName_3237_ = _args[19];
lean_object* v___x_3238_ = _args[20];
lean_object* v_brecOnEqName_3239_ = _args[21];
lean_object* v_fs_3240_ = _args[22];
lean_object* v___y_3241_ = _args[23];
lean_object* v___y_3242_ = _args[24];
lean_object* v___y_3243_ = _args[25];
lean_object* v___y_3244_ = _args[26];
lean_object* v___y_3245_ = _args[27];
_start:
{
size_t v_sz_boxed_3246_; size_t v___x_30769__boxed_3247_; uint8_t v___x_30777__boxed_3248_; lean_object* v_res_3249_; 
v_sz_boxed_3246_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v___x_30769__boxed_3247_ = lean_unbox_usize(v___x_3225_);
lean_dec(v___x_3225_);
v___x_30777__boxed_3248_ = lean_unbox(v___x_3233_);
v_res_3249_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3218_, v_tail_3219_, v_recName_3220_, v___x_3221_, v___x_3222_, v___x_3223_, v_sz_boxed_3246_, v___x_30769__boxed_3247_, v___x_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v___x_3231_, v_val_3232_, v___x_30777__boxed_3248_, v_brecOnGoName_3234_, v_levelParams_3235_, v___x_3236_, v_brecOnName_3237_, v___x_3238_, v_brecOnEqName_3239_, v_fs_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___x_3238_);
lean_dec(v_val_3232_);
lean_dec_ref(v___x_3231_);
lean_dec(v___x_3230_);
lean_dec_ref(v___x_3226_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3250_, lean_object* v_a_3251_, uint8_t v___x_3252_, lean_object* v_f_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3264_, lean_object* v_a_3265_, lean_object* v___x_3266_, lean_object* v_f_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v___x_31487__boxed_3273_; lean_object* v_res_3274_; 
v___x_31487__boxed_3273_ = lean_unbox(v___x_3266_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3264_, v_a_3265_, v___x_31487__boxed_3273_, v_f_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3278_, uint8_t v___x_3279_, lean_object* v___x_3280_, lean_object* v_targs_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3288_ = lean_box(v___x_3279_);
lean_inc_ref(v_targs_3281_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3289_, 0, v_targs_3281_);
lean_closure_set(v___f_3289_, 1, v_a_3278_);
lean_closure_set(v___f_3289_, 2, v___x_3288_);
v___x_3290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3291_ = l_Lean_mkAppN(v___x_3280_, v_targs_3281_);
lean_dec_ref(v_targs_3281_);
v___x_3292_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3290_, v___x_3291_, v___f_3289_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3293_, lean_object* v___x_3294_, lean_object* v___x_3295_, lean_object* v_targs_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v___x_31521__boxed_3303_; lean_object* v_res_3304_; 
v___x_31521__boxed_3303_ = lean_unbox(v___x_3294_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3293_, v___x_31521__boxed_3303_, v___x_3295_, v_targs_3296_, v_x_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec_ref(v_x_3297_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_a_3305_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_x_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v_as_3322_, size_t v_sz_3323_, size_t v_i_3324_, lean_object* v_b_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_usize_dec_lt(v_i_3324_, v_sz_3323_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; 
v___x_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3332_, 0, v_b_3325_);
return v___x_3332_;
}
else
{
lean_object* v_snd_3333_; lean_object* v_fst_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3430_; 
v_snd_3333_ = lean_ctor_get(v_b_3325_, 1);
v_fst_3334_ = lean_ctor_get(v_b_3325_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_b_3325_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3336_ = v_b_3325_;
v_isShared_3337_ = v_isSharedCheck_3430_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_snd_3333_);
lean_inc(v_fst_3334_);
lean_dec(v_b_3325_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3430_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v_fst_3338_; lean_object* v_snd_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3429_; 
v_fst_3338_ = lean_ctor_get(v_snd_3333_, 0);
v_snd_3339_ = lean_ctor_get(v_snd_3333_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_snd_3333_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3341_ = v_snd_3333_;
v_isShared_3342_ = v_isSharedCheck_3429_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_snd_3339_);
lean_inc(v_fst_3338_);
lean_dec(v_snd_3333_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3429_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v_next_3351_; 
v_next_3351_ = lean_ctor_get(v_snd_3339_, 0);
lean_inc(v_next_3351_);
if (lean_obj_tag(v_next_3351_) == 0)
{
goto v___jp_3343_;
}
else
{
lean_object* v_upperBound_3352_; lean_object* v_val_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3428_; 
v_upperBound_3352_ = lean_ctor_get(v_snd_3339_, 1);
v_val_3353_ = lean_ctor_get(v_next_3351_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_next_3351_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3355_ = v_next_3351_;
v_isShared_3356_ = v_isSharedCheck_3428_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_val_3353_);
lean_dec(v_next_3351_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3428_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_nat_dec_lt(v_val_3353_, v_upperBound_3352_);
if (v___x_3357_ == 0)
{
lean_del_object(v___x_3355_);
lean_dec(v_val_3353_);
goto v___jp_3343_;
}
else
{
lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3425_; 
lean_inc(v_upperBound_3352_);
lean_del_object(v___x_3341_);
lean_del_object(v___x_3336_);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_snd_3339_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; 
v_unused_3426_ = lean_ctor_get(v_snd_3339_, 1);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_snd_3339_, 0);
lean_dec(v_unused_3427_);
v___x_3359_ = v_snd_3339_;
v_isShared_3360_ = v_isSharedCheck_3425_;
goto v_resetjp_3358_;
}
else
{
lean_dec(v_snd_3339_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3425_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_array_3361_; lean_object* v_start_3362_; lean_object* v_stop_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
v_array_3361_ = lean_ctor_get(v_fst_3338_, 0);
v_start_3362_ = lean_ctor_get(v_fst_3338_, 1);
v_stop_3363_ = lean_ctor_get(v_fst_3338_, 2);
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = lean_nat_add(v_val_3353_, v___x_3364_);
lean_dec(v_val_3353_);
lean_inc(v___x_3365_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3365_);
v___x_3367_ = v___x_3355_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3365_);
v___x_3367_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3367_);
v___x_3369_ = v___x_3359_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3367_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_upperBound_3352_);
v___x_3369_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_nat_dec_lt(v_start_3362_, v_stop_3363_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
lean_dec(v___x_3365_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_fst_3338_);
lean_ctor_set(v___x_3371_, 1, v___x_3369_);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_fst_3334_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
return v___x_3373_;
}
else
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3419_; 
lean_inc(v_stop_3363_);
lean_inc(v_start_3362_);
lean_inc_ref(v_array_3361_);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_fst_3338_);
if (v_isSharedCheck_3419_ == 0)
{
lean_object* v_unused_3420_; lean_object* v_unused_3421_; lean_object* v_unused_3422_; 
v_unused_3420_ = lean_ctor_get(v_fst_3338_, 2);
lean_dec(v_unused_3420_);
v_unused_3421_ = lean_ctor_get(v_fst_3338_, 1);
lean_dec(v_unused_3421_);
v_unused_3422_ = lean_ctor_get(v_fst_3338_, 0);
lean_dec(v_unused_3422_);
v___x_3375_ = v_fst_3338_;
v_isShared_3376_ = v_isSharedCheck_3419_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_fst_3338_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3419_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_array_uget_borrowed(v_as_3322_, v_i_3324_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc(v___y_3327_);
lean_inc_ref(v___y_3326_);
lean_inc(v_a_3377_);
v___x_3378_ = lean_infer_type(v_a_3377_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___f_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = lean_array_fget_borrowed(v_array_3361_, v_start_3362_);
v___x_3381_ = lean_box(v___x_3370_);
lean_inc(v___x_3380_);
lean_inc(v_a_3377_);
v___f_3382_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3382_, 0, v_a_3377_);
lean_closure_set(v___f_3382_, 1, v___x_3381_);
lean_closure_set(v___f_3382_, 2, v___x_3380_);
v___x_3383_ = 0;
v___x_3384_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3379_, v___f_3382_, v___x_3383_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___f_3386_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3386_, 0, v_a_3385_);
v___x_3387_ = lean_nat_add(v_start_3362_, v___x_3364_);
lean_dec(v_start_3362_);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 1, v___x_3387_);
v___x_3389_ = v___x_3375_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_array_3361_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_stop_3363_);
v___x_3389_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; size_t v___x_3399_; size_t v___x_3400_; 
v___x_3390_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3391_ = l_Nat_reprFast(v___x_3365_);
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
lean_dec_ref(v___x_3391_);
v___x_3393_ = lean_box(0);
v___x_3394_ = l_Lean_Name_str___override(v___x_3393_, v___x_3392_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___f_3386_);
v___x_3396_ = lean_array_push(v_fst_3334_, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3389_);
lean_ctor_set(v___x_3397_, 1, v___x_3369_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = ((size_t)1ULL);
v___x_3400_ = lean_usize_add(v_i_3324_, v___x_3399_);
v_i_3324_ = v___x_3400_;
v_b_3325_ = v___x_3398_;
goto _start;
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_del_object(v___x_3375_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3365_);
lean_dec(v_stop_3363_);
lean_dec(v_start_3362_);
lean_dec_ref(v_array_3361_);
lean_dec(v_fst_3334_);
v_a_3403_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3384_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3384_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3375_);
lean_dec_ref(v___x_3369_);
lean_dec(v___x_3365_);
lean_dec(v_stop_3363_);
lean_dec(v_start_3362_);
lean_dec_ref(v_array_3361_);
lean_dec(v_fst_3334_);
v_a_3411_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3378_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3378_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
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
v___jp_3343_:
{
lean_object* v___x_3345_; 
if (v_isShared_3342_ == 0)
{
v___x_3345_ = v___x_3341_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_fst_3338_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_snd_3339_);
v___x_3345_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 1, v___x_3345_);
v___x_3347_ = v___x_3336_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_fst_3334_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3345_);
v___x_3347_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v_as_3431_, lean_object* v_sz_3432_, lean_object* v_i_3433_, lean_object* v_b_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
size_t v_sz_boxed_3440_; size_t v_i_boxed_3441_; lean_object* v_res_3442_; 
v_sz_boxed_3440_ = lean_unbox_usize(v_sz_3432_);
lean_dec(v_sz_3432_);
v_i_boxed_3441_ = lean_unbox_usize(v_i_3433_);
lean_dec(v_i_3433_);
v_res_3442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v_as_3431_, v_sz_boxed_3440_, v_i_boxed_3441_, v_b_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec_ref(v_as_3431_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3443_, size_t v_i_3444_, lean_object* v_bs_3445_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3444_, v_sz_3443_);
if (v___x_3446_ == 0)
{
return v_bs_3445_;
}
else
{
lean_object* v_v_3447_; lean_object* v_fst_3448_; lean_object* v_snd_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3465_; 
v_v_3447_ = lean_array_uget(v_bs_3445_, v_i_3444_);
v_fst_3448_ = lean_ctor_get(v_v_3447_, 0);
v_snd_3449_ = lean_ctor_get(v_v_3447_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_v_3447_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3451_ = v_v_3447_;
v_isShared_3452_ = v_isSharedCheck_3465_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snd_3449_);
lean_inc(v_fst_3448_);
lean_dec(v_v_3447_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3465_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v_bs_x27_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3453_ = lean_unsigned_to_nat(0u);
v_bs_x27_3454_ = lean_array_uset(v_bs_3445_, v_i_3444_, v___x_3453_);
v___x_3455_ = 0;
v___x_3456_ = lean_box(v___x_3455_);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 0, v___x_3456_);
v___x_3458_ = v___x_3451_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_snd_3449_);
v___x_3458_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; size_t v___x_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_fst_3448_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = ((size_t)1ULL);
v___x_3461_ = lean_usize_add(v_i_3444_, v___x_3460_);
v___x_3462_ = lean_array_uset(v_bs_x27_3454_, v_i_3444_, v___x_3459_);
v_i_3444_ = v___x_3461_;
v_bs_3445_ = v___x_3462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3466_, lean_object* v_i_3467_, lean_object* v_bs_3468_){
_start:
{
size_t v_sz_boxed_3469_; size_t v_i_boxed_3470_; lean_object* v_res_3471_; 
v_sz_boxed_3469_ = lean_unbox_usize(v_sz_3466_);
lean_dec(v_sz_3466_);
v_i_boxed_3470_ = lean_unbox_usize(v_i_3467_);
lean_dec(v_i_3467_);
v_res_3471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3469_, v_i_boxed_3470_, v_bs_3468_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3472_, lean_object* v_a_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_30330__overap_3480_; lean_object* v___x_3481_; 
v___x_3479_ = l_Lean_instInhabitedExpr;
v___x_30330__overap_3480_ = l_instInhabitedOfMonad___redArg(v___x_3472_, v___x_3479_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
v___x_3481_ = lean_apply_5(v___x_30330__overap_3480_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, lean_box(0));
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3482_, lean_object* v_a_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3482_, v_a_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v_a_3483_);
return v_res_3489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3490_; 
v___x_3490_ = l_instMonadEIO(lean_box(0));
return v___x_3490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3492_ = l_StateRefT_x27_instMonad___redArg(v___x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3497_, lean_object* v_declInfos_3498_, lean_object* v_k_3499_, lean_object* v_kind_3500_, lean_object* v_b_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
uint8_t v_kind_boxed_3507_; lean_object* v_res_3508_; 
v_kind_boxed_3507_ = lean_unbox(v_kind_3500_);
v_res_3508_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3497_, v_declInfos_3498_, v_k_3499_, v_kind_boxed_3507_, v_b_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3509_, lean_object* v_declInfos_3510_, lean_object* v_k_3511_, uint8_t v_kind_3512_, lean_object* v_name_3513_, uint8_t v_bi_3514_, lean_object* v_type_3515_, uint8_t v_kind_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
lean_object* v___x_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_box(v_kind_3512_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3523_, 0, v_acc_3509_);
lean_closure_set(v___f_3523_, 1, v_declInfos_3510_);
lean_closure_set(v___f_3523_, 2, v_k_3511_);
lean_closure_set(v___f_3523_, 3, v___x_3522_);
v___x_3524_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3513_, v_bi_3514_, v_type_3515_, v___f_3523_, v_kind_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3524_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3524_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
v_a_3533_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3524_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3524_);
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
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3541_, lean_object* v_k_3542_, uint8_t v_kind_3543_, lean_object* v_acc_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v_toApplicative_3551_; lean_object* v_toFunctor_3552_; lean_object* v_toSeq_3553_; lean_object* v_toSeqLeft_3554_; lean_object* v_toSeqRight_3555_; lean_object* v___f_3556_; lean_object* v___f_3557_; lean_object* v___f_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___f_3561_; lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_toApplicative_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3622_; 
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3551_ = lean_ctor_get(v___x_3550_, 0);
v_toFunctor_3552_ = lean_ctor_get(v_toApplicative_3551_, 0);
v_toSeq_3553_ = lean_ctor_get(v_toApplicative_3551_, 2);
v_toSeqLeft_3554_ = lean_ctor_get(v_toApplicative_3551_, 3);
v_toSeqRight_3555_ = lean_ctor_get(v_toApplicative_3551_, 4);
v___f_3556_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3557_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3552_, 2);
v___f_3558_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3558_, 0, v_toFunctor_3552_);
v___f_3559_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3559_, 0, v_toFunctor_3552_);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___f_3558_);
lean_ctor_set(v___x_3560_, 1, v___f_3559_);
lean_inc(v_toSeqRight_3555_);
v___f_3561_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3561_, 0, v_toSeqRight_3555_);
lean_inc(v_toSeqLeft_3554_);
v___f_3562_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3562_, 0, v_toSeqLeft_3554_);
lean_inc(v_toSeq_3553_);
v___f_3563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3563_, 0, v_toSeq_3553_);
v___x_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3560_);
lean_ctor_set(v___x_3564_, 1, v___f_3556_);
lean_ctor_set(v___x_3564_, 2, v___f_3563_);
lean_ctor_set(v___x_3564_, 3, v___f_3562_);
lean_ctor_set(v___x_3564_, 4, v___f_3561_);
v___x_3565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v___f_3557_);
v___x_3566_ = l_StateRefT_x27_instMonad___redArg(v___x_3565_);
v_toApplicative_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3566_, 1);
lean_dec(v_unused_3623_);
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3622_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_toApplicative_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3622_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v_toFunctor_3571_; lean_object* v_toSeq_3572_; lean_object* v_toSeqLeft_3573_; lean_object* v_toSeqRight_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3620_; 
v_toFunctor_3571_ = lean_ctor_get(v_toApplicative_3567_, 0);
v_toSeq_3572_ = lean_ctor_get(v_toApplicative_3567_, 2);
v_toSeqLeft_3573_ = lean_ctor_get(v_toApplicative_3567_, 3);
v_toSeqRight_3574_ = lean_ctor_get(v_toApplicative_3567_, 4);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_toApplicative_3567_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; 
v_unused_3621_ = lean_ctor_get(v_toApplicative_3567_, 1);
lean_dec(v_unused_3621_);
v___x_3576_ = v_toApplicative_3567_;
v_isShared_3577_ = v_isSharedCheck_3620_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_toSeqRight_3574_);
lean_inc(v_toSeqLeft_3573_);
lean_inc(v_toSeq_3572_);
lean_inc(v_toFunctor_3571_);
lean_dec(v_toApplicative_3567_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3620_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___f_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___x_3587_; 
v___f_3578_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3579_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3571_);
v___f_3580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3580_, 0, v_toFunctor_3571_);
v___f_3581_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3581_, 0, v_toFunctor_3571_);
v___x_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3582_, 0, v___f_3580_);
lean_ctor_set(v___x_3582_, 1, v___f_3581_);
v___f_3583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3583_, 0, v_toSeqRight_3574_);
v___f_3584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3584_, 0, v_toSeqLeft_3573_);
v___f_3585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3585_, 0, v_toSeq_3572_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 4, v___f_3583_);
lean_ctor_set(v___x_3576_, 3, v___f_3584_);
lean_ctor_set(v___x_3576_, 2, v___f_3585_);
lean_ctor_set(v___x_3576_, 1, v___f_3578_);
lean_ctor_set(v___x_3576_, 0, v___x_3582_);
v___x_3587_ = v___x_3576_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___f_3578_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v___f_3585_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v___f_3584_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v___f_3583_);
v___x_3587_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3589_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 1, v___f_3579_);
lean_ctor_set(v___x_3569_, 0, v___x_3587_);
v___x_3589_ = v___x_3569_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___f_3579_);
v___x_3589_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3590_ = lean_array_get_size(v_acc_3544_);
v___x_3591_ = lean_array_get_size(v_declInfos_3541_);
v___x_3592_ = lean_nat_dec_lt(v___x_3590_, v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; 
lean_dec_ref(v___x_3589_);
lean_dec_ref(v_declInfos_3541_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
v___x_3593_ = lean_apply_6(v_k_3542_, v_acc_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, lean_box(0));
return v___x_3593_;
}
else
{
lean_object* v___f_3594_; lean_object* v___x_3595_; uint8_t v___x_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v_snd_3602_; lean_object* v_fst_3603_; lean_object* v_fst_3604_; lean_object* v_snd_3605_; lean_object* v___x_3606_; 
v___f_3594_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3594_, 0, v___x_3589_);
v___x_3595_ = lean_box(0);
v___x_3596_ = 0;
v___f_3597_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3597_, 0, v___f_3594_);
v___x_3598_ = lean_box(v___x_3596_);
v___x_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3598_);
lean_ctor_set(v___x_3599_, 1, v___f_3597_);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3595_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_array_get(v___x_3600_, v_declInfos_3541_, v___x_3590_);
lean_dec_ref_known(v___x_3600_, 2);
v_snd_3602_ = lean_ctor_get(v___x_3601_, 1);
lean_inc(v_snd_3602_);
v_fst_3603_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_fst_3603_);
lean_dec(v___x_3601_);
v_fst_3604_ = lean_ctor_get(v_snd_3602_, 0);
lean_inc(v_fst_3604_);
v_snd_3605_ = lean_ctor_get(v_snd_3602_, 1);
lean_inc(v_snd_3605_);
lean_dec(v_snd_3602_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc_ref(v_acc_3544_);
v___x_3606_ = lean_apply_6(v_snd_3605_, v_acc_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, lean_box(0));
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v___x_3608_ = lean_unbox(v_fst_3604_);
lean_dec(v_fst_3604_);
v___x_3609_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3544_, v_declInfos_3541_, v_k_3542_, v_kind_3543_, v_fst_3603_, v___x_3608_, v_a_3607_, v_kind_3543_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3609_;
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_fst_3604_);
lean_dec(v_fst_3603_);
lean_dec_ref(v_acc_3544_);
lean_dec_ref(v_k_3542_);
lean_dec_ref(v_declInfos_3541_);
v_a_3610_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3606_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3606_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3624_, lean_object* v_declInfos_3625_, lean_object* v_k_3626_, uint8_t v_kind_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_array_push(v_acc_3624_, v_b_3628_);
v___x_3635_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3625_, v_k_3626_, v_kind_3627_, v___x_3634_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3636_, lean_object* v_declInfos_3637_, lean_object* v_k_3638_, lean_object* v_kind_3639_, lean_object* v_name_3640_, lean_object* v_bi_3641_, lean_object* v_type_3642_, lean_object* v_kind_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
uint8_t v_kind_boxed_3649_; uint8_t v_bi_boxed_3650_; uint8_t v_kind_boxed_3651_; lean_object* v_res_3652_; 
v_kind_boxed_3649_ = lean_unbox(v_kind_3639_);
v_bi_boxed_3650_ = lean_unbox(v_bi_3641_);
v_kind_boxed_3651_ = lean_unbox(v_kind_3643_);
v_res_3652_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3636_, v_declInfos_3637_, v_k_3638_, v_kind_boxed_3649_, v_name_3640_, v_bi_boxed_3650_, v_type_3642_, v_kind_boxed_3651_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3653_, lean_object* v_k_3654_, lean_object* v_kind_3655_, lean_object* v_acc_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
uint8_t v_kind_boxed_3662_; lean_object* v_res_3663_; 
v_kind_boxed_3662_ = lean_unbox(v_kind_3655_);
v_res_3663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3653_, v_k_3654_, v_kind_boxed_3662_, v_acc_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3664_, lean_object* v_k_3665_, uint8_t v_kind_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3664_, v_k_3665_, v_kind_3666_, v___x_3672_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3674_, lean_object* v_k_3675_, lean_object* v_kind_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
uint8_t v_kind_boxed_3682_; lean_object* v_res_3683_; 
v_kind_boxed_3682_ = lean_unbox(v_kind_3676_);
v_res_3683_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3674_, v_k_3675_, v_kind_boxed_3682_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec(v___y_3678_);
lean_dec_ref(v___y_3677_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3684_, lean_object* v_k_3685_, uint8_t v_kind_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
size_t v_sz_3692_; size_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_sz_3692_ = lean_array_size(v_declInfos_3684_);
v___x_3693_ = ((size_t)0ULL);
v___x_3694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3692_, v___x_3693_, v_declInfos_3684_);
v___x_3695_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3694_, v_k_3685_, v_kind_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3696_, lean_object* v_k_3697_, lean_object* v_kind_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v_kind_boxed_3704_; lean_object* v_res_3705_; 
v_kind_boxed_3704_ = lean_unbox(v_kind_3698_);
v_res_3705_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3696_, v_k_3697_, v_kind_boxed_3704_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
return v_res_3705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3708_ = lean_unsigned_to_nat(4u);
v___x_3709_ = lean_unsigned_to_nat(202u);
v___x_3710_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3711_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3712_ = l_mkPanicMessageWithDecl(v___x_3711_, v___x_3710_, v___x_3709_, v___x_3708_, v___x_3707_);
return v___x_3712_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
return v___x_3719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3725_, lean_object* v_numMotives_3726_, lean_object* v_numMinors_3727_, lean_object* v___x_3728_, lean_object* v_all_3729_, lean_object* v_head_3730_, lean_object* v_tail_3731_, lean_object* v_recName_3732_, lean_object* v_brecOnGoName_3733_, lean_object* v_levelParams_3734_, lean_object* v_brecOnName_3735_, lean_object* v_brecOnEqName_3736_, lean_object* v_type_3737_, lean_object* v_refArgs_3738_, lean_object* v_refBody_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3745_ = lean_nat_add(v_nParams_3725_, v_numMotives_3726_);
v___x_3746_ = lean_nat_add(v___x_3745_, v_numMinors_3727_);
v___x_3747_ = lean_array_get_size(v_refArgs_3738_);
v___x_3748_ = lean_nat_dec_lt(v___x_3746_, v___x_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec_ref(v_type_3737_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
lean_dec(v_nParams_3725_);
v___x_3749_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3750_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3749_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3750_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3751_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3725_);
lean_inc_ref_n(v_refArgs_3738_, 2);
v___x_3752_ = l_Array_toSubarray___redArg(v_refArgs_3738_, v___x_3751_, v_nParams_3725_);
lean_inc(v___x_3745_);
v___x_3753_ = l_Array_toSubarray___redArg(v_refArgs_3738_, v_nParams_3725_, v___x_3745_);
v___x_3754_ = l_Subarray_copy___redArg(v___x_3753_);
v___x_3755_ = l_Lean_Expr_getAppFn(v_refBody_3739_);
v___x_3756_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3754_, v___x_3755_);
lean_dec_ref(v___x_3755_);
if (lean_obj_tag(v___x_3756_) == 1)
{
lean_object* v_val_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
lean_dec_ref(v_type_3737_);
v_val_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_val_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = l_Lean_instInhabitedExpr;
v___x_3759_ = lean_unsigned_to_nat(1u);
v___x_3760_ = lean_nat_sub(v___x_3747_, v___x_3759_);
v___x_3761_ = lean_array_get(v___x_3758_, v_refArgs_3738_, v___x_3760_);
lean_inc(v___y_3743_);
lean_inc_ref(v___y_3742_);
lean_inc(v___y_3741_);
lean_inc_ref(v___y_3740_);
lean_inc(v___x_3761_);
v___x_3762_ = lean_infer_type(v___x_3761_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3764_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
lean_inc(v_a_3763_);
lean_dec_ref_known(v___x_3762_, 1);
lean_inc(v___y_3743_);
lean_inc_ref(v___y_3742_);
lean_inc(v___y_3741_);
lean_inc_ref(v___y_3740_);
v___x_3764_ = lean_infer_type(v_a_3763_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v___x_3766_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3765_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
if (lean_obj_tag(v_a_3767_) == 1)
{
lean_object* v_val_3768_; lean_object* v___x_3769_; lean_object* v___f_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; size_t v_sz_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v_val_3768_ = lean_ctor_get(v_a_3767_, 0);
lean_inc(v_val_3768_);
lean_dec_ref_known(v_a_3767_, 1);
v___x_3769_ = l_Subarray_copy___redArg(v___x_3752_);
lean_inc_ref(v___x_3754_);
lean_inc_ref(v___x_3769_);
lean_inc(v___x_3728_);
v___f_3770_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3770_, 0, v___x_3728_);
lean_closure_set(v___f_3770_, 1, v___x_3769_);
lean_closure_set(v___f_3770_, 2, v___x_3754_);
lean_closure_set(v___f_3770_, 3, v_all_3729_);
lean_closure_set(v___f_3770_, 4, v___x_3751_);
lean_closure_set(v___f_3770_, 5, v___x_3759_);
v___x_3771_ = lean_array_get_size(v___x_3754_);
v___x_3772_ = l_Array_ofFn___redArg(v___x_3771_, v___f_3770_);
v___x_3773_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3774_ = lean_array_get_size(v___x_3772_);
lean_inc_ref(v___x_3772_);
v___x_3775_ = l_Array_toSubarray___redArg(v___x_3772_, v___x_3751_, v___x_3774_);
v___x_3776_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
lean_ctor_set(v___x_3777_, 1, v___x_3771_);
lean_inc_ref(v___x_3775_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3775_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3773_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v_sz_3780_ = lean_array_size(v___x_3754_);
v___x_3781_ = ((size_t)0ULL);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3754_, v_sz_3780_, v___x_3781_, v___x_3779_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v_fst_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___f_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
v_fst_3784_ = lean_ctor_get(v_a_3783_, 0);
lean_inc(v_fst_3784_);
lean_dec(v_a_3783_);
lean_inc(v___x_3746_);
lean_inc_ref(v_refArgs_3738_);
v___x_3785_ = l_Array_toSubarray___redArg(v_refArgs_3738_, v___x_3745_, v___x_3746_);
v___x_3786_ = l_Subarray_copy___redArg(v___x_3785_);
v___x_3787_ = l_Array_toSubarray___redArg(v_refArgs_3738_, v___x_3746_, v___x_3760_);
v___x_3788_ = l_Subarray_copy___redArg(v___x_3787_);
v___x_3789_ = l_Lean_mkLevelMax(v_val_3768_, v_head_3730_);
v___x_3790_ = lean_box_usize(v_sz_3780_);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3792_ = lean_box(v___x_3748_);
v___f_3793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3793_, 0, v___x_3789_);
lean_closure_set(v___f_3793_, 1, v_tail_3731_);
lean_closure_set(v___f_3793_, 2, v_recName_3732_);
lean_closure_set(v___f_3793_, 3, v___x_3769_);
lean_closure_set(v___f_3793_, 4, v___x_3775_);
lean_closure_set(v___f_3793_, 5, v___x_3754_);
lean_closure_set(v___f_3793_, 6, v___x_3790_);
lean_closure_set(v___f_3793_, 7, v___x_3791_);
lean_closure_set(v___f_3793_, 8, v___x_3786_);
lean_closure_set(v___f_3793_, 9, v___x_3772_);
lean_closure_set(v___f_3793_, 10, v___x_3788_);
lean_closure_set(v___f_3793_, 11, v___x_3761_);
lean_closure_set(v___f_3793_, 12, v___x_3759_);
lean_closure_set(v___f_3793_, 13, v___x_3758_);
lean_closure_set(v___f_3793_, 14, v_val_3757_);
lean_closure_set(v___f_3793_, 15, v___x_3792_);
lean_closure_set(v___f_3793_, 16, v_brecOnGoName_3733_);
lean_closure_set(v___f_3793_, 17, v_levelParams_3734_);
lean_closure_set(v___f_3793_, 18, v___x_3728_);
lean_closure_set(v___f_3793_, 19, v_brecOnName_3735_);
lean_closure_set(v___f_3793_, 20, v___x_3751_);
lean_closure_set(v___f_3793_, 21, v_brecOnEqName_3736_);
v___x_3794_ = 0;
v___x_3795_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3784_, v___f_3793_, v___x_3794_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3795_;
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v___x_3775_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___x_3769_);
lean_dec(v_val_3768_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec(v_val_3757_);
lean_dec_ref(v___x_3754_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec(v___x_3728_);
v_a_3796_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3782_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3782_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec(v_a_3767_);
lean_dec(v___x_3760_);
lean_dec(v_val_3757_);
lean_dec_ref(v___x_3754_);
lean_dec_ref(v___x_3752_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
v___x_3804_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3805_ = l_Lean_MessageData_ofExpr(v___x_3761_);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3808_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3809_;
}
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec(v_val_3757_);
lean_dec_ref(v___x_3754_);
lean_dec_ref(v___x_3752_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
v_a_3810_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3766_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3766_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec(v_val_3757_);
lean_dec_ref(v___x_3754_);
lean_dec_ref(v___x_3752_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
v_a_3818_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3764_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3764_);
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
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec(v_val_3757_);
lean_dec_ref(v___x_3754_);
lean_dec_ref(v___x_3752_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
v_a_3826_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3762_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3762_);
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
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec(v___x_3756_);
lean_dec_ref(v___x_3752_);
lean_dec(v___x_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_refArgs_3738_);
lean_dec(v_brecOnEqName_3736_);
lean_dec(v_brecOnName_3735_);
lean_dec(v_levelParams_3734_);
lean_dec(v_brecOnGoName_3733_);
lean_dec(v_recName_3732_);
lean_dec(v_tail_3731_);
lean_dec(v_head_3730_);
lean_dec_ref(v_all_3729_);
lean_dec(v___x_3728_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3835_ = l_Lean_MessageData_ofExpr(v_type_3737_);
v___x_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_array_to_list(v___x_3754_);
v___x_3840_ = lean_box(0);
v___x_3841_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3839_, v___x_3840_);
v___x_3842_ = l_Lean_MessageData_ofList(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3838_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3843_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
return v___x_3844_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3845_ = _args[0];
lean_object* v_numMotives_3846_ = _args[1];
lean_object* v_numMinors_3847_ = _args[2];
lean_object* v___x_3848_ = _args[3];
lean_object* v_all_3849_ = _args[4];
lean_object* v_head_3850_ = _args[5];
lean_object* v_tail_3851_ = _args[6];
lean_object* v_recName_3852_ = _args[7];
lean_object* v_brecOnGoName_3853_ = _args[8];
lean_object* v_levelParams_3854_ = _args[9];
lean_object* v_brecOnName_3855_ = _args[10];
lean_object* v_brecOnEqName_3856_ = _args[11];
lean_object* v_type_3857_ = _args[12];
lean_object* v_refArgs_3858_ = _args[13];
lean_object* v_refBody_3859_ = _args[14];
lean_object* v___y_3860_ = _args[15];
lean_object* v___y_3861_ = _args[16];
lean_object* v___y_3862_ = _args[17];
lean_object* v___y_3863_ = _args[18];
lean_object* v___y_3864_ = _args[19];
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3845_, v_numMotives_3846_, v_numMinors_3847_, v___x_3848_, v_all_3849_, v_head_3850_, v_tail_3851_, v_recName_3852_, v_brecOnGoName_3853_, v_levelParams_3854_, v_brecOnName_3855_, v_brecOnEqName_3856_, v_type_3857_, v_refArgs_3858_, v_refBody_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec_ref(v_refBody_3859_);
lean_dec(v_numMinors_3847_);
lean_dec(v_numMotives_3846_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3868_, lean_object* v_nParams_3869_, lean_object* v_all_3870_, lean_object* v_brecOnName_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3877_; 
lean_inc(v_recName_3868_);
v___x_3877_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3868_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3909_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3909_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3909_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
if (lean_obj_tag(v_a_3878_) == 7)
{
lean_object* v_val_3882_; lean_object* v_toConstantVal_3883_; lean_object* v_numMotives_3884_; lean_object* v_numMinors_3885_; lean_object* v_levelParams_3886_; lean_object* v_type_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_del_object(v___x_3880_);
v_val_3882_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_ref(v_val_3882_);
lean_dec_ref_known(v_a_3878_, 1);
v_toConstantVal_3883_ = lean_ctor_get(v_val_3882_, 0);
lean_inc_ref(v_toConstantVal_3883_);
v_numMotives_3884_ = lean_ctor_get(v_val_3882_, 4);
lean_inc(v_numMotives_3884_);
v_numMinors_3885_ = lean_ctor_get(v_val_3882_, 5);
lean_inc(v_numMinors_3885_);
lean_dec_ref(v_val_3882_);
v_levelParams_3886_ = lean_ctor_get(v_toConstantVal_3883_, 1);
lean_inc_n(v_levelParams_3886_, 2);
v_type_3887_ = lean_ctor_get(v_toConstantVal_3883_, 2);
lean_inc_ref(v_type_3887_);
lean_dec_ref(v_toConstantVal_3883_);
v___x_3888_ = lean_box(0);
v___x_3889_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3886_, v___x_3888_);
if (lean_obj_tag(v___x_3889_) == 1)
{
lean_object* v_head_3890_; lean_object* v_tail_3891_; lean_object* v___x_3892_; lean_object* v_brecOnGoName_3893_; lean_object* v___x_3894_; lean_object* v_brecOnEqName_3895_; lean_object* v___f_3896_; uint8_t v___x_3897_; lean_object* v___x_3898_; 
v_head_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_head_3890_);
v_tail_3891_ = lean_ctor_get(v___x_3889_, 1);
lean_inc(v_tail_3891_);
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3871_, 2);
v_brecOnGoName_3893_ = l_Lean_Name_str___override(v_brecOnName_3871_, v___x_3892_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3895_ = l_Lean_Name_str___override(v_brecOnName_3871_, v___x_3894_);
lean_inc_ref(v_type_3887_);
v___f_3896_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 20, 13);
lean_closure_set(v___f_3896_, 0, v_nParams_3869_);
lean_closure_set(v___f_3896_, 1, v_numMotives_3884_);
lean_closure_set(v___f_3896_, 2, v_numMinors_3885_);
lean_closure_set(v___f_3896_, 3, v___x_3889_);
lean_closure_set(v___f_3896_, 4, v_all_3870_);
lean_closure_set(v___f_3896_, 5, v_head_3890_);
lean_closure_set(v___f_3896_, 6, v_tail_3891_);
lean_closure_set(v___f_3896_, 7, v_recName_3868_);
lean_closure_set(v___f_3896_, 8, v_brecOnGoName_3893_);
lean_closure_set(v___f_3896_, 9, v_levelParams_3886_);
lean_closure_set(v___f_3896_, 10, v_brecOnName_3871_);
lean_closure_set(v___f_3896_, 11, v_brecOnEqName_3895_);
lean_closure_set(v___f_3896_, 12, v_type_3887_);
v___x_3897_ = 0;
v___x_3898_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3887_, v___f_3896_, v___x_3897_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
return v___x_3898_;
}
else
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v___x_3889_);
lean_dec_ref(v_type_3887_);
lean_dec(v_levelParams_3886_);
lean_dec(v_numMinors_3885_);
lean_dec(v_numMotives_3884_);
lean_dec(v_brecOnName_3871_);
lean_dec_ref(v_all_3870_);
lean_dec(v_nParams_3869_);
v___x_3899_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3900_ = l_Lean_MessageData_ofName(v_recName_3868_);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3901_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
v___x_3904_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3903_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
return v___x_3904_;
}
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
lean_dec(v_a_3878_);
lean_dec(v_brecOnName_3871_);
lean_dec_ref(v_all_3870_);
lean_dec(v_nParams_3869_);
lean_dec(v_recName_3868_);
v___x_3905_ = lean_box(0);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v___x_3905_);
v___x_3907_ = v___x_3880_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_dec(v_brecOnName_3871_);
lean_dec_ref(v_all_3870_);
lean_dec(v_nParams_3869_);
lean_dec(v_recName_3868_);
v_a_3910_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3877_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3877_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3918_, lean_object* v_nParams_3919_, lean_object* v_all_3920_, lean_object* v_brecOnName_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3918_, v_nParams_3919_, v_all_3920_, v_brecOnName_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec_ref(v_a_3922_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3928_, lean_object* v___x_3929_, lean_object* v___x_3930_, lean_object* v___x_3931_, lean_object* v___x_3932_, lean_object* v_a_3933_, lean_object* v_b_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
uint8_t v___x_3940_; 
v___x_3940_ = lean_nat_dec_lt(v_a_3933_, v_upperBound_3928_);
if (v___x_3940_ == 0)
{
lean_object* v___x_3941_; 
lean_dec(v_a_3933_);
lean_dec_ref(v___x_3932_);
lean_dec(v___x_3931_);
lean_dec(v___x_3930_);
lean_dec(v___x_3929_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_b_3934_);
return v___x_3941_;
}
else
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3942_ = lean_unsigned_to_nat(1u);
v___x_3943_ = lean_nat_add(v_a_3933_, v___x_3942_);
lean_dec(v_a_3933_);
lean_inc_n(v___x_3943_, 2);
lean_inc(v___x_3929_);
v___x_3944_ = lean_name_append_index_after(v___x_3929_, v___x_3943_);
lean_inc(v___x_3930_);
v___x_3945_ = lean_name_append_index_after(v___x_3930_, v___x_3943_);
lean_inc_ref(v___x_3932_);
lean_inc(v___x_3931_);
v___x_3946_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3944_, v___x_3931_, v___x_3932_, v___x_3945_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v___x_3947_; 
lean_dec_ref_known(v___x_3946_, 1);
v___x_3947_ = lean_box(0);
v_a_3933_ = v___x_3943_;
v_b_3934_ = v___x_3947_;
goto _start;
}
else
{
lean_dec(v___x_3943_);
lean_dec_ref(v___x_3932_);
lean_dec(v___x_3931_);
lean_dec(v___x_3930_);
lean_dec(v___x_3929_);
return v___x_3946_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3949_, lean_object* v___x_3950_, lean_object* v___x_3951_, lean_object* v___x_3952_, lean_object* v___x_3953_, lean_object* v_a_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3949_, v___x_3950_, v___x_3951_, v___x_3952_, v___x_3953_, v_a_3954_, v_b_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v_upperBound_3949_);
return v_res_3961_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3967_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3968_ = l_Lean_Name_append(v___x_3967_, v___x_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_options_3975_; uint8_t v_hasTrace_3976_; 
v_options_3975_ = lean_ctor_get(v_a_3972_, 2);
v_hasTrace_3976_ = lean_ctor_get_uint8(v_options_3975_, sizeof(void*)*1);
if (v_hasTrace_3976_ == 0)
{
lean_object* v___x_3977_; 
lean_inc(v_indName_3969_);
v___x_3977_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_4043_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_3980_ = v___x_3977_;
v_isShared_3981_ = v_isSharedCheck_4043_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3977_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_4043_;
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
lean_dec(v_indName_3969_);
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
v___x_3993_ = l_Lean_Meta_isPropFormerType(v_type_3992_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4030_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4030_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4030_;
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
lean_inc_n(v_indName_3969_, 2);
v___x_3999_ = l_Lean_mkRecName(v_indName_3969_);
v___x_4000_ = l_Lean_mkBRecOnName(v_indName_3969_);
lean_inc(v_all_3990_);
v___x_4001_ = lean_array_mk(v_all_3990_);
lean_inc(v___x_4000_);
lean_inc_ref(v___x_4001_);
lean_inc(v_numParams_3989_);
lean_inc(v___x_3999_);
v___x_4002_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3999_, v_numParams_3989_, v___x_4001_, v___x_4000_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4024_; 
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v___x_4002_, 0);
lean_dec(v_unused_4025_);
v___x_4004_ = v___x_4002_;
v_isShared_4005_ = v_isSharedCheck_4024_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v___x_4002_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4024_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4006_ = lean_box(0);
v___x_4007_ = lean_unsigned_to_nat(0u);
v___x_4008_ = l_List_get_x21Internal___redArg(v___x_4006_, v_all_3990_, v___x_4007_);
lean_dec(v_all_3990_);
v___x_4009_ = lean_name_eq(v___x_4008_, v_indName_3969_);
lean_dec(v_indName_3969_);
lean_dec(v___x_4008_);
if (v___x_4009_ == 0)
{
lean_object* v___x_4010_; lean_object* v___x_4012_; 
lean_dec_ref(v___x_4001_);
lean_dec(v___x_4000_);
lean_dec(v___x_3999_);
lean_dec(v_numNested_3991_);
lean_dec(v_numParams_3989_);
v___x_4010_ = lean_box(0);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v___x_4010_);
v___x_4012_ = v___x_4004_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v___x_4010_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_del_object(v___x_4004_);
v___x_4014_ = lean_box(0);
v___x_4015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_3991_, v___x_3999_, v___x_4000_, v_numParams_3989_, v___x_4001_, v___x_4007_, v___x_4014_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_numNested_3991_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; 
v_unused_4023_ = lean_ctor_get(v___x_4015_, 0);
lean_dec(v_unused_4023_);
v___x_4017_ = v___x_4015_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_dec(v___x_4015_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4014_);
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4014_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
else
{
return v___x_4015_;
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
lean_dec(v_indName_3969_);
return v___x_4002_;
}
}
else
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
lean_dec(v_numNested_3991_);
lean_dec(v_all_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_indName_3969_);
v___x_4026_ = lean_box(0);
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v___x_4026_);
v___x_4028_ = v___x_3996_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v_numNested_3991_);
lean_dec(v_all_3990_);
lean_dec(v_numParams_3989_);
lean_dec(v_indName_3969_);
v_a_4031_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_3993_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_3993_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
else
{
lean_object* v___x_4039_; lean_object* v___x_4041_; 
lean_dec(v_a_3978_);
lean_dec(v_indName_3969_);
v___x_4039_ = lean_box(0);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_4039_);
v___x_4041_ = v___x_3980_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4039_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_indName_3969_);
v_a_4044_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_3977_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_3977_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4052_; lean_object* v___f_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v_a_4061_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v_a_4076_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v_a_4086_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v_a_4098_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v_a_4103_; 
v_inheritedTraceOptions_4052_ = lean_ctor_get(v_a_3972_, 13);
lean_inc(v_indName_3969_);
v___f_4053_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4053_, 0, v_indName_3969_);
v___x_4054_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4055_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4056_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4052_, v_options_3975_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4174_; uint8_t v___x_4175_; 
v___x_4174_ = l_Lean_trace_profiler;
v___x_4175_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3975_, v___x_4174_);
if (v___x_4175_ == 0)
{
lean_object* v___x_4176_; 
lean_dec_ref(v___f_4053_);
lean_inc(v_indName_3969_);
v___x_4176_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4242_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4242_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4242_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
if (lean_obj_tag(v_a_4177_) == 5)
{
lean_object* v_val_4181_; uint8_t v_isRec_4182_; 
v_val_4181_ = lean_ctor_get(v_a_4177_, 0);
lean_inc_ref(v_val_4181_);
lean_dec_ref_known(v_a_4177_, 1);
v_isRec_4182_ = lean_ctor_get_uint8(v_val_4181_, sizeof(void*)*6);
if (v_isRec_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4185_; 
lean_dec_ref(v_val_4181_);
lean_dec(v_indName_3969_);
v___x_4183_ = lean_box(0);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4183_);
v___x_4185_ = v___x_4179_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
else
{
lean_object* v_toConstantVal_4187_; lean_object* v_numParams_4188_; lean_object* v_all_4189_; lean_object* v_numNested_4190_; lean_object* v_type_4191_; lean_object* v___x_4192_; 
lean_del_object(v___x_4179_);
v_toConstantVal_4187_ = lean_ctor_get(v_val_4181_, 0);
lean_inc_ref(v_toConstantVal_4187_);
v_numParams_4188_ = lean_ctor_get(v_val_4181_, 1);
lean_inc(v_numParams_4188_);
v_all_4189_ = lean_ctor_get(v_val_4181_, 3);
lean_inc(v_all_4189_);
v_numNested_4190_ = lean_ctor_get(v_val_4181_, 5);
lean_inc(v_numNested_4190_);
lean_dec_ref(v_val_4181_);
v_type_4191_ = lean_ctor_get(v_toConstantVal_4187_, 2);
lean_inc_ref(v_type_4191_);
lean_dec_ref(v_toConstantVal_4187_);
v___x_4192_ = l_Lean_Meta_isPropFormerType(v_type_4191_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4229_; 
v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4195_ = v___x_4192_;
v_isShared_4196_ = v_isSharedCheck_4229_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4192_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4229_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_unbox(v_a_4193_);
lean_dec(v_a_4193_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
lean_del_object(v___x_4195_);
lean_inc_n(v_indName_3969_, 2);
v___x_4198_ = l_Lean_mkRecName(v_indName_3969_);
v___x_4199_ = l_Lean_mkBRecOnName(v_indName_3969_);
lean_inc(v_all_4189_);
v___x_4200_ = lean_array_mk(v_all_4189_);
lean_inc(v___x_4199_);
lean_inc_ref(v___x_4200_);
lean_inc(v_numParams_4188_);
lean_inc(v___x_4198_);
v___x_4201_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4198_, v_numParams_4188_, v___x_4200_, v___x_4199_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4223_; 
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4223_ == 0)
{
lean_object* v_unused_4224_; 
v_unused_4224_ = lean_ctor_get(v___x_4201_, 0);
lean_dec(v_unused_4224_);
v___x_4203_ = v___x_4201_;
v_isShared_4204_ = v_isSharedCheck_4223_;
goto v_resetjp_4202_;
}
else
{
lean_dec(v___x_4201_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4223_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; 
v___x_4205_ = lean_box(0);
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = l_List_get_x21Internal___redArg(v___x_4205_, v_all_4189_, v___x_4206_);
lean_dec(v_all_4189_);
v___x_4208_ = lean_name_eq(v___x_4207_, v_indName_3969_);
lean_dec(v_indName_3969_);
lean_dec(v___x_4207_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
lean_dec_ref(v___x_4200_);
lean_dec(v___x_4199_);
lean_dec(v___x_4198_);
lean_dec(v_numNested_4190_);
lean_dec(v_numParams_4188_);
v___x_4209_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4209_);
v___x_4211_ = v___x_4203_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v___x_4209_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_del_object(v___x_4203_);
v___x_4213_ = lean_box(0);
v___x_4214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4190_, v___x_4198_, v___x_4199_, v_numParams_4188_, v___x_4200_, v___x_4206_, v___x_4213_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_numNested_4190_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4221_ == 0)
{
lean_object* v_unused_4222_; 
v_unused_4222_ = lean_ctor_get(v___x_4214_, 0);
lean_dec(v_unused_4222_);
v___x_4216_ = v___x_4214_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_dec(v___x_4214_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4213_);
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4213_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
else
{
return v___x_4214_;
}
}
}
}
else
{
lean_dec_ref(v___x_4200_);
lean_dec(v___x_4199_);
lean_dec(v___x_4198_);
lean_dec(v_numNested_4190_);
lean_dec(v_all_4189_);
lean_dec(v_numParams_4188_);
lean_dec(v_indName_3969_);
return v___x_4201_;
}
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4227_; 
lean_dec(v_numNested_4190_);
lean_dec(v_all_4189_);
lean_dec(v_numParams_4188_);
lean_dec(v_indName_3969_);
v___x_4225_ = lean_box(0);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 0, v___x_4225_);
v___x_4227_ = v___x_4195_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v_numNested_4190_);
lean_dec(v_all_4189_);
lean_dec(v_numParams_4188_);
lean_dec(v_indName_3969_);
v_a_4230_ = lean_ctor_get(v___x_4192_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4192_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4192_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4192_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
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
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4240_; 
lean_dec(v_a_4177_);
lean_dec(v_indName_3969_);
v___x_4238_ = lean_box(0);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4238_);
v___x_4240_ = v___x_4179_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4238_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_indName_3969_);
v_a_4243_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4176_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4176_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
else
{
goto v___jp_4105_;
}
}
else
{
goto v___jp_4105_;
}
v___jp_4058_:
{
lean_object* v___x_4062_; double v___x_4063_; double v___x_4064_; double v___x_4065_; double v___x_4066_; double v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4062_ = lean_io_mono_nanos_now();
v___x_4063_ = lean_float_of_nat(v___y_4060_);
v___x_4064_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4065_ = lean_float_div(v___x_4063_, v___x_4064_);
v___x_4066_ = lean_float_of_nat(v___x_4062_);
v___x_4067_ = lean_float_div(v___x_4066_, v___x_4064_);
v___x_4068_ = lean_box_float(v___x_4065_);
v___x_4069_ = lean_box_float(v___x_4067_);
v___x_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4068_);
lean_ctor_set(v___x_4070_, 1, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_a_4061_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4054_, v_hasTrace_3976_, v___x_4055_, v_options_3975_, v___x_4057_, v___y_4059_, v___f_4053_, v___x_4071_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4072_;
}
v___jp_4073_:
{
lean_object* v___x_4077_; 
v___x_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4077_, 0, v_a_4076_);
v___y_4059_ = v___y_4074_;
v___y_4060_ = v___y_4075_;
v_a_4061_ = v___x_4077_;
goto v___jp_4058_;
}
v___jp_4078_:
{
lean_object* v___x_4082_; 
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v_a_4081_);
v___y_4059_ = v___y_4079_;
v___y_4060_ = v___y_4080_;
v_a_4061_ = v___x_4082_;
goto v___jp_4058_;
}
v___jp_4083_:
{
lean_object* v___x_4087_; double v___x_4088_; double v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4087_ = lean_io_get_num_heartbeats();
v___x_4088_ = lean_float_of_nat(v___y_4085_);
v___x_4089_ = lean_float_of_nat(v___x_4087_);
v___x_4090_ = lean_box_float(v___x_4088_);
v___x_4091_ = lean_box_float(v___x_4089_);
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4093_, 0, v_a_4086_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4054_, v_hasTrace_3976_, v___x_4055_, v_options_3975_, v___x_4057_, v___y_4084_, v___f_4053_, v___x_4093_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_4094_;
}
v___jp_4095_:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_a_4098_);
v___y_4084_ = v___y_4096_;
v___y_4085_ = v___y_4097_;
v_a_4086_ = v___x_4099_;
goto v___jp_4083_;
}
v___jp_4100_:
{
lean_object* v___x_4104_; 
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v_a_4103_);
v___y_4084_ = v___y_4101_;
v___y_4085_ = v___y_4102_;
v_a_4086_ = v___x_4104_;
goto v___jp_4083_;
}
v___jp_4105_:
{
lean_object* v___x_4106_; lean_object* v_a_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v___x_4106_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3973_);
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref(v___x_4106_);
v___x_4108_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4109_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3975_, v___x_4108_);
if (v___x_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3969_);
v___x_4111_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
if (lean_obj_tag(v_a_4112_) == 5)
{
lean_object* v_val_4113_; uint8_t v_isRec_4114_; 
v_val_4113_ = lean_ctor_get(v_a_4112_, 0);
lean_inc_ref(v_val_4113_);
lean_dec_ref_known(v_a_4112_, 1);
v_isRec_4114_ = lean_ctor_get_uint8(v_val_4113_, sizeof(void*)*6);
if (v_isRec_4114_ == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref(v_val_4113_);
lean_dec(v_indName_3969_);
v___x_4115_ = lean_box(0);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v___x_4115_;
goto v___jp_4073_;
}
else
{
lean_object* v_toConstantVal_4116_; lean_object* v_numParams_4117_; lean_object* v_all_4118_; lean_object* v_numNested_4119_; lean_object* v_type_4120_; lean_object* v___x_4121_; 
v_toConstantVal_4116_ = lean_ctor_get(v_val_4113_, 0);
lean_inc_ref(v_toConstantVal_4116_);
v_numParams_4117_ = lean_ctor_get(v_val_4113_, 1);
lean_inc(v_numParams_4117_);
v_all_4118_ = lean_ctor_get(v_val_4113_, 3);
lean_inc(v_all_4118_);
v_numNested_4119_ = lean_ctor_get(v_val_4113_, 5);
lean_inc(v_numNested_4119_);
lean_dec_ref(v_val_4113_);
v_type_4120_ = lean_ctor_get(v_toConstantVal_4116_, 2);
lean_inc_ref(v_type_4120_);
lean_dec_ref(v_toConstantVal_4116_);
v___x_4121_ = l_Lean_Meta_isPropFormerType(v_type_4120_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; uint8_t v___x_4123_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref_known(v___x_4121_, 1);
v___x_4123_ = lean_unbox(v_a_4122_);
lean_dec(v_a_4122_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_inc_n(v_indName_3969_, 2);
v___x_4124_ = l_Lean_mkRecName(v_indName_3969_);
v___x_4125_ = l_Lean_mkBRecOnName(v_indName_3969_);
lean_inc(v_all_4118_);
v___x_4126_ = lean_array_mk(v_all_4118_);
lean_inc(v___x_4125_);
lean_inc_ref(v___x_4126_);
lean_inc(v_numParams_4117_);
lean_inc(v___x_4124_);
v___x_4127_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4124_, v_numParams_4117_, v___x_4126_, v___x_4125_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; uint8_t v___x_4131_; 
lean_dec_ref_known(v___x_4127_, 1);
v___x_4128_ = lean_box(0);
v___x_4129_ = lean_unsigned_to_nat(0u);
v___x_4130_ = l_List_get_x21Internal___redArg(v___x_4128_, v_all_4118_, v___x_4129_);
lean_dec(v_all_4118_);
v___x_4131_ = lean_name_eq(v___x_4130_, v_indName_3969_);
lean_dec(v_indName_3969_);
lean_dec(v___x_4130_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; 
lean_dec_ref(v___x_4126_);
lean_dec(v___x_4125_);
lean_dec(v___x_4124_);
lean_dec(v_numNested_4119_);
lean_dec(v_numParams_4117_);
v___x_4132_ = lean_box(0);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v___x_4132_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = lean_box(0);
v___x_4134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4119_, v___x_4124_, v___x_4125_, v_numParams_4117_, v___x_4126_, v___x_4129_, v___x_4133_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_numNested_4119_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v___x_4133_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4135_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4135_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4079_ = v_a_4107_;
v___y_4080_ = v___x_4110_;
v_a_4081_ = v_a_4135_;
goto v___jp_4078_;
}
}
}
else
{
lean_dec_ref(v___x_4126_);
lean_dec(v___x_4125_);
lean_dec(v___x_4124_);
lean_dec(v_numNested_4119_);
lean_dec(v_all_4118_);
lean_dec(v_numParams_4117_);
lean_dec(v_indName_3969_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4136_; 
v_a_4136_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4127_, 1);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v_a_4136_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4137_; 
v_a_4137_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4127_, 1);
v___y_4079_ = v_a_4107_;
v___y_4080_ = v___x_4110_;
v_a_4081_ = v_a_4137_;
goto v___jp_4078_;
}
}
}
else
{
lean_object* v___x_4138_; 
lean_dec(v_numNested_4119_);
lean_dec(v_all_4118_);
lean_dec(v_numParams_4117_);
lean_dec(v_indName_3969_);
v___x_4138_ = lean_box(0);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v___x_4138_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4139_; 
lean_dec(v_numNested_4119_);
lean_dec(v_all_4118_);
lean_dec(v_numParams_4117_);
lean_dec(v_indName_3969_);
v_a_4139_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4121_, 1);
v___y_4079_ = v_a_4107_;
v___y_4080_ = v___x_4110_;
v_a_4081_ = v_a_4139_;
goto v___jp_4078_;
}
}
}
else
{
lean_object* v___x_4140_; 
lean_dec(v_a_4112_);
lean_dec(v_indName_3969_);
v___x_4140_ = lean_box(0);
v___y_4074_ = v_a_4107_;
v___y_4075_ = v___x_4110_;
v_a_4076_ = v___x_4140_;
goto v___jp_4073_;
}
}
else
{
lean_object* v_a_4141_; 
lean_dec(v_indName_3969_);
v_a_4141_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4111_, 1);
v___y_4079_ = v_a_4107_;
v___y_4080_ = v___x_4110_;
v_a_4081_ = v_a_4141_;
goto v___jp_4078_;
}
}
else
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3969_);
v___x_4143_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
if (lean_obj_tag(v_a_4144_) == 5)
{
lean_object* v_val_4145_; uint8_t v_isRec_4146_; 
v_val_4145_ = lean_ctor_get(v_a_4144_, 0);
lean_inc_ref(v_val_4145_);
lean_dec_ref_known(v_a_4144_, 1);
v_isRec_4146_ = lean_ctor_get_uint8(v_val_4145_, sizeof(void*)*6);
if (v_isRec_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_dec_ref(v_val_4145_);
lean_dec(v_indName_3969_);
v___x_4147_ = lean_box(0);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v___x_4147_;
goto v___jp_4095_;
}
else
{
lean_object* v_toConstantVal_4148_; lean_object* v_numParams_4149_; lean_object* v_all_4150_; lean_object* v_numNested_4151_; lean_object* v_type_4152_; lean_object* v___x_4153_; 
v_toConstantVal_4148_ = lean_ctor_get(v_val_4145_, 0);
lean_inc_ref(v_toConstantVal_4148_);
v_numParams_4149_ = lean_ctor_get(v_val_4145_, 1);
lean_inc(v_numParams_4149_);
v_all_4150_ = lean_ctor_get(v_val_4145_, 3);
lean_inc(v_all_4150_);
v_numNested_4151_ = lean_ctor_get(v_val_4145_, 5);
lean_inc(v_numNested_4151_);
lean_dec_ref(v_val_4145_);
v_type_4152_ = lean_ctor_get(v_toConstantVal_4148_, 2);
lean_inc_ref(v_type_4152_);
lean_dec_ref(v_toConstantVal_4148_);
v___x_4153_ = l_Lean_Meta_isPropFormerType(v_type_4152_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; uint8_t v___x_4155_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = lean_unbox(v_a_4154_);
lean_dec(v_a_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
lean_inc_n(v_indName_3969_, 2);
v___x_4156_ = l_Lean_mkRecName(v_indName_3969_);
v___x_4157_ = l_Lean_mkBRecOnName(v_indName_3969_);
lean_inc(v_all_4150_);
v___x_4158_ = lean_array_mk(v_all_4150_);
lean_inc(v___x_4157_);
lean_inc_ref(v___x_4158_);
lean_inc(v_numParams_4149_);
lean_inc(v___x_4156_);
v___x_4159_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4156_, v_numParams_4149_, v___x_4158_, v___x_4157_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
lean_dec_ref_known(v___x_4159_, 1);
v___x_4160_ = lean_box(0);
v___x_4161_ = lean_unsigned_to_nat(0u);
v___x_4162_ = l_List_get_x21Internal___redArg(v___x_4160_, v_all_4150_, v___x_4161_);
lean_dec(v_all_4150_);
v___x_4163_ = lean_name_eq(v___x_4162_, v_indName_3969_);
lean_dec(v_indName_3969_);
lean_dec(v___x_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; 
lean_dec_ref(v___x_4158_);
lean_dec(v___x_4157_);
lean_dec(v___x_4156_);
lean_dec(v_numNested_4151_);
lean_dec(v_numParams_4149_);
v___x_4164_ = lean_box(0);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v___x_4164_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = lean_box(0);
v___x_4166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4151_, v___x_4156_, v___x_4157_, v_numParams_4149_, v___x_4158_, v___x_4161_, v___x_4165_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_numNested_4151_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_dec_ref_known(v___x_4166_, 1);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v___x_4165_;
goto v___jp_4095_;
}
else
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___y_4101_ = v_a_4107_;
v___y_4102_ = v___x_4142_;
v_a_4103_ = v_a_4167_;
goto v___jp_4100_;
}
}
}
else
{
lean_dec_ref(v___x_4158_);
lean_dec(v___x_4157_);
lean_dec(v___x_4156_);
lean_dec(v_numNested_4151_);
lean_dec(v_all_4150_);
lean_dec(v_numParams_4149_);
lean_dec(v_indName_3969_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4168_; 
v_a_4168_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4159_, 1);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v_a_4168_;
goto v___jp_4095_;
}
else
{
lean_object* v_a_4169_; 
v_a_4169_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4159_, 1);
v___y_4101_ = v_a_4107_;
v___y_4102_ = v___x_4142_;
v_a_4103_ = v_a_4169_;
goto v___jp_4100_;
}
}
}
else
{
lean_object* v___x_4170_; 
lean_dec(v_numNested_4151_);
lean_dec(v_all_4150_);
lean_dec(v_numParams_4149_);
lean_dec(v_indName_3969_);
v___x_4170_ = lean_box(0);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v___x_4170_;
goto v___jp_4095_;
}
}
else
{
lean_object* v_a_4171_; 
lean_dec(v_numNested_4151_);
lean_dec(v_all_4150_);
lean_dec(v_numParams_4149_);
lean_dec(v_indName_3969_);
v_a_4171_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4101_ = v_a_4107_;
v___y_4102_ = v___x_4142_;
v_a_4103_ = v_a_4171_;
goto v___jp_4100_;
}
}
}
else
{
lean_object* v___x_4172_; 
lean_dec(v_a_4144_);
lean_dec(v_indName_3969_);
v___x_4172_ = lean_box(0);
v___y_4096_ = v_a_4107_;
v___y_4097_ = v___x_4142_;
v_a_4098_ = v___x_4172_;
goto v___jp_4095_;
}
}
else
{
lean_object* v_a_4173_; 
lean_dec(v_indName_3969_);
v_a_4173_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4143_, 1);
v___y_4101_ = v_a_4107_;
v___y_4102_ = v___x_4142_;
v_a_4103_ = v_a_4173_;
goto v___jp_4100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_mkBRecOn(v_indName_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
lean_dec_ref(v_a_4252_);
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4258_, lean_object* v___x_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v___x_4262_, lean_object* v_inst_4263_, lean_object* v_R_4264_, lean_object* v_a_4265_, lean_object* v_b_4266_, lean_object* v_c_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4258_, v___x_4259_, v___x_4260_, v___x_4261_, v___x_4262_, v_a_4265_, v_b_4266_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4274_, lean_object* v___x_4275_, lean_object* v___x_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v_inst_4279_, lean_object* v_R_4280_, lean_object* v_a_4281_, lean_object* v_b_4282_, lean_object* v_c_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4274_, v___x_4275_, v___x_4276_, v___x_4277_, v___x_4278_, v_inst_4279_, v_R_4280_, v_a_4281_, v_b_4282_, v_c_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v_upperBound_4274_);
return v_res_4289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4335_ = lean_unsigned_to_nat(2304625798u);
v___x_4336_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4337_ = l_Lean_Name_num___override(v___x_4336_, v___x_4335_);
return v___x_4337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4340_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4341_ = l_Lean_Name_str___override(v___x_4340_, v___x_4339_);
return v___x_4341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4344_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4345_ = l_Lean_Name_str___override(v___x_4344_, v___x_4343_);
return v___x_4345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4346_ = lean_unsigned_to_nat(2u);
v___x_4347_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4348_ = l_Lean_Name_num___override(v___x_4347_, v___x_4346_);
return v___x_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4350_; uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4350_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4351_ = 0;
v___x_4352_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4353_ = l_Lean_registerTraceClass(v___x_4350_, v___x_4351_, v___x_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4355_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_PProdN(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_BRecOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
