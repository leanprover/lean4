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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1_value;
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
uint8_t v___x_1933__boxed_100_; lean_object* v_res_101_; 
v___x_1933__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_1933__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
uint8_t v___x_2088__boxed_251_; uint8_t v___x_2089__boxed_252_; lean_object* v_res_253_; 
v___x_2088__boxed_251_ = lean_unbox(v___x_239_);
v___x_2089__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2088__boxed_251_, v___x_2089__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
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
uint8_t v___x_9024__boxed_555_; lean_object* v_res_556_; 
v___x_9024__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9024__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_object* v_a_571_; lean_object* v___x_572_; 
v_a_571_ = lean_array_uget_borrowed(v_as_560_, v_i_562_);
lean_inc(v___y_567_);
lean_inc_ref(v___y_566_);
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v_a_571_);
v___x_572_ = lean_infer_type(v_a_571_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; uint8_t v___x_574_; lean_object* v___x_575_; lean_object* v___f_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_572_, 1);
v___x_574_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
v___x_575_ = lean_box(v___x_574_);
lean_inc(v___x_557_);
v___f_576_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_576_, 0, v___x_557_);
lean_closure_set(v___f_576_, 1, v___x_575_);
v___x_577_ = 0;
v___x_578_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_573_, v___f_576_, v___x_577_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
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
lean_dec_ref(v_b_563_);
lean_dec(v___x_557_);
return v___x_572_;
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
lean_object* v___x_605_; lean_object* v_env_606_; lean_object* v___x_607_; lean_object* v_mctx_608_; lean_object* v_lctx_609_; lean_object* v_options_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_605_ = lean_st_ref_get(v___y_603_);
v_env_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc_ref(v_env_606_);
lean_dec(v___x_605_);
v___x_607_ = lean_st_ref_get(v___y_601_);
v_mctx_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc_ref(v_mctx_608_);
lean_dec(v___x_607_);
v_lctx_609_ = lean_ctor_get(v___y_600_, 2);
v_options_610_ = lean_ctor_get(v___y_602_, 1);
lean_inc_ref(v_options_610_);
lean_inc_ref(v_lctx_609_);
v___x_611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_611_, 0, v_env_606_);
lean_ctor_set(v___x_611_, 1, v_mctx_608_);
lean_ctor_set(v___x_611_, 2, v_lctx_609_);
lean_ctor_set(v___x_611_, 3, v_options_610_);
v___x_612_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_msgData_599_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7___boxed(lean_object* v_msgData_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msgData_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(lean_object* v_msg_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_ref_627_; lean_object* v___x_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
v_ref_627_ = lean_ctor_get(v___y_624_, 4);
v___x_628_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v_ref_627_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_ref_627_);
lean_ctor_set(v___x_633_, 1, v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set_tag(v___x_631_, 1);
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg___boxed(lean_object* v_msg_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
return v_res_644_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_648_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_unsigned_to_nat(68u);
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__1));
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_653_ = l_mkPanicMessageWithDecl(v___x_652_, v___x_651_, v___x_650_, v___x_649_, v___x_648_);
return v___x_653_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__4));
v___x_656_ = l_Lean_stringToMessageData(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__6));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(lean_object* v_nParams_660_, lean_object* v_numMotives_661_, lean_object* v_numMinors_662_, lean_object* v___x_663_, lean_object* v_head_664_, lean_object* v_tail_665_, lean_object* v_recName_666_, lean_object* v_belowName_667_, lean_object* v_levelParams_668_, lean_object* v_refArgs_669_, lean_object* v_x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_676_ = lean_nat_add(v_nParams_660_, v_numMotives_661_);
v___x_677_ = lean_nat_add(v___x_676_, v_numMinors_662_);
v___x_678_ = lean_array_get_size(v_refArgs_669_);
v___x_679_ = lean_nat_dec_lt(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
lean_dec(v_recName_666_);
lean_dec(v_tail_665_);
lean_dec(v_head_664_);
lean_dec(v_nParams_660_);
v___x_680_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__3);
v___x_681_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v___x_680_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_660_);
lean_inc_ref(v_refArgs_669_);
v___x_683_ = l_Array_toSubarray___redArg(v_refArgs_669_, v___x_682_, v_nParams_660_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_sub(v___x_678_, v___x_684_);
v___x_686_ = lean_array_get(v___x_663_, v_refArgs_669_, v___x_685_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
lean_inc(v___x_686_);
v___x_687_ = lean_infer_type(v___x_686_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
lean_inc(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_689_ = lean_infer_type(v_a_688_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = l_Lean_Meta_typeFormerTypeLevel(v_a_690_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
if (lean_obj_tag(v_a_692_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; size_t v_sz_703_; size_t v___x_704_; lean_object* v___x_705_; 
v_val_693_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v_a_692_, 1);
lean_inc(v___x_676_);
lean_inc_ref_n(v_refArgs_669_, 2);
v___x_694_ = l_Array_toSubarray___redArg(v_refArgs_669_, v_nParams_660_, v___x_676_);
lean_inc(v___x_677_);
v___x_695_ = l_Array_toSubarray___redArg(v_refArgs_669_, v___x_676_, v___x_677_);
v___x_696_ = l_Subarray_copy___redArg(v___x_683_);
v___x_697_ = l_Subarray_copy___redArg(v___x_694_);
v___x_698_ = l_Lean_mkLevelMax(v_val_693_, v_head_664_);
lean_inc_n(v___x_698_, 2);
v___x_699_ = l_Lean_Level_succ___override(v___x_698_);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_tail_665_);
v___x_701_ = l_Lean_Expr_const___override(v_recName_666_, v___x_700_);
v___x_702_ = l_Lean_mkAppN(v___x_701_, v___x_696_);
v_sz_703_ = lean_array_size(v___x_697_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_698_, v___x_677_, v___x_678_, v___x_697_, v_sz_703_, v___x_704_, v___x_702_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; size_t v_sz_708_; lean_object* v___x_709_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = l_Subarray_copy___redArg(v___x_695_);
v_sz_708_ = lean_array_size(v___x_707_);
lean_inc_ref(v___x_697_);
lean_inc(v___x_698_);
v___x_709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_698_, v___x_697_, v___x_707_, v_sz_708_, v___x_704_, v_a_706_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec_ref(v___x_707_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Array_toSubarray___redArg(v_refArgs_669_, v___x_677_, v___x_685_);
v___x_712_ = l_Subarray_copy___redArg(v___x_711_);
v___x_713_ = l_Lean_mkAppN(v_a_710_, v___x_712_);
lean_inc(v___x_686_);
v___x_714_ = l_Lean_Expr_app___override(v___x_713_, v___x_686_);
v___x_715_ = l_Array_append___redArg(v___x_696_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_716_ = l_Array_append___redArg(v___x_715_, v___x_712_);
lean_dec_ref(v___x_712_);
v___x_717_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_718_ = lean_array_push(v___x_717_, v___x_686_);
v___x_719_ = l_Array_append___redArg(v___x_716_, v___x_718_);
lean_dec_ref(v___x_718_);
v___x_720_ = l_Lean_Expr_sort___override(v___x_698_);
v___x_721_ = 0;
v___x_722_ = 1;
v___x_723_ = l_Lean_Meta_mkForallFVars(v___x_719_, v___x_720_, v___x_721_, v___x_679_, v___x_679_, v___x_722_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = l_Lean_Meta_mkLambdaFVars(v___x_719_, v___x_714_, v___x_721_, v___x_679_, v___x_721_, v___x_679_, v___x_722_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec_ref(v___x_719_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_box(1);
v___x_728_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_667_, v_levelParams_668_, v_a_724_, v_a_726_, v___x_727_, v___y_674_);
return v___x_728_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v_a_724_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
v_a_729_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_725_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_725_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec_ref(v___x_719_);
lean_dec_ref(v___x_714_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
v_a_737_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_723_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_723_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_696_);
lean_dec(v___x_686_);
lean_dec(v___x_685_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
v_a_745_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_709_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_709_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_695_);
lean_dec(v___x_686_);
lean_dec(v___x_685_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
v_a_753_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_705_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_705_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v_a_692_);
lean_dec(v___x_685_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
lean_dec(v_recName_666_);
lean_dec(v_tail_665_);
lean_dec(v_head_664_);
lean_dec(v_nParams_660_);
v___x_761_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_762_ = l_Lean_MessageData_ofExpr(v___x_686_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_765_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_766_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v___x_686_);
lean_dec(v___x_685_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
lean_dec(v_recName_666_);
lean_dec(v_tail_665_);
lean_dec(v_head_664_);
lean_dec(v_nParams_660_);
v_a_767_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_691_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_691_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v___x_686_);
lean_dec(v___x_685_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
lean_dec(v_recName_666_);
lean_dec(v_tail_665_);
lean_dec(v_head_664_);
lean_dec(v_nParams_660_);
v_a_775_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_689_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_689_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v___x_686_);
lean_dec(v___x_685_);
lean_dec_ref(v___x_683_);
lean_dec(v___x_677_);
lean_dec(v___x_676_);
lean_dec_ref(v_refArgs_669_);
lean_dec(v_levelParams_668_);
lean_dec(v_belowName_667_);
lean_dec(v_recName_666_);
lean_dec(v_tail_665_);
lean_dec(v_head_664_);
lean_dec(v_nParams_660_);
v_a_783_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_687_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_687_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed(lean_object* v_nParams_791_, lean_object* v_numMotives_792_, lean_object* v_numMinors_793_, lean_object* v___x_794_, lean_object* v_head_795_, lean_object* v_tail_796_, lean_object* v_recName_797_, lean_object* v_belowName_798_, lean_object* v_levelParams_799_, lean_object* v_refArgs_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0(v_nParams_791_, v_numMotives_792_, v_numMinors_793_, v___x_794_, v_head_795_, v_tail_796_, v_recName_797_, v_belowName_798_, v_levelParams_799_, v_refArgs_800_, v_x_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_x_801_);
lean_dec_ref(v___x_794_);
lean_dec(v_numMinors_793_);
lean_dec(v_numMotives_792_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = l_List_reverse___redArg(v_a_809_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_head_811_ = lean_ctor_get(v_a_808_, 0);
v_tail_812_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_816_ = l_Lean_Level_param___override(v_head_811_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_a_809_);
lean_ctor_set(v___x_814_, 0, v___x_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_809_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_808_ = v_tail_812_;
v_a_809_ = v___x_818_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_822_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__0);
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__1);
v___x_828_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
lean_ctor_set(v___x_828_, 4, v___x_827_);
lean_ctor_set(v___x_828_, 5, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(lean_object* v_declName_829_, uint8_t v_s_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v_env_835_; lean_object* v_nextMacroScope_836_; lean_object* v_ngen_837_; lean_object* v_auxDeclNGen_838_; lean_object* v_traceState_839_; lean_object* v_messages_840_; lean_object* v_infoState_841_; lean_object* v_snapshotTasks_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_871_; 
v___x_834_ = lean_st_ref_take(v___y_832_);
v_env_835_ = lean_ctor_get(v___x_834_, 0);
v_nextMacroScope_836_ = lean_ctor_get(v___x_834_, 1);
v_ngen_837_ = lean_ctor_get(v___x_834_, 2);
v_auxDeclNGen_838_ = lean_ctor_get(v___x_834_, 3);
v_traceState_839_ = lean_ctor_get(v___x_834_, 4);
v_messages_840_ = lean_ctor_get(v___x_834_, 6);
v_infoState_841_ = lean_ctor_get(v___x_834_, 7);
v_snapshotTasks_842_ = lean_ctor_get(v___x_834_, 8);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v___x_834_, 5);
lean_dec(v_unused_872_);
v___x_844_ = v___x_834_;
v_isShared_845_ = v_isSharedCheck_871_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snapshotTasks_842_);
lean_inc(v_infoState_841_);
lean_inc(v_messages_840_);
lean_inc(v_traceState_839_);
lean_inc(v_auxDeclNGen_838_);
lean_inc(v_ngen_837_);
lean_inc(v_nextMacroScope_836_);
lean_inc(v_env_835_);
lean_dec(v___x_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_871_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_846_ = 0;
v___x_847_ = lean_box(0);
v___x_848_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_835_, v_declName_829_, v_s_830_, v___x_846_, v___x_847_);
v___x_849_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 5, v___x_849_);
lean_ctor_set(v___x_844_, 0, v___x_848_);
v___x_851_ = v___x_844_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_nextMacroScope_836_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_ngen_837_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_auxDeclNGen_838_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_traceState_839_);
lean_ctor_set(v_reuseFailAlloc_870_, 5, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_870_, 6, v_messages_840_);
lean_ctor_set(v_reuseFailAlloc_870_, 7, v_infoState_841_);
lean_ctor_set(v_reuseFailAlloc_870_, 8, v_snapshotTasks_842_);
v___x_851_ = v_reuseFailAlloc_870_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_mctx_854_; lean_object* v_zetaDeltaFVarIds_855_; lean_object* v_postponed_856_; lean_object* v_diag_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_868_; 
v___x_852_ = lean_st_ref_put(v___y_832_, v___x_851_);
v___x_853_ = lean_st_ref_take(v___y_831_);
v_mctx_854_ = lean_ctor_get(v___x_853_, 0);
v_zetaDeltaFVarIds_855_ = lean_ctor_get(v___x_853_, 2);
v_postponed_856_ = lean_ctor_get(v___x_853_, 3);
v_diag_857_ = lean_ctor_get(v___x_853_, 4);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v___x_853_, 1);
lean_dec(v_unused_869_);
v___x_859_ = v___x_853_;
v_isShared_860_ = v_isSharedCheck_868_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_diag_857_);
lean_inc(v_postponed_856_);
lean_inc(v_zetaDeltaFVarIds_855_);
lean_inc(v_mctx_854_);
lean_dec(v___x_853_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_868_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_861_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_861_);
v___x_863_ = v___x_859_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_mctx_854_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_zetaDeltaFVarIds_855_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_postponed_856_);
lean_ctor_set(v_reuseFailAlloc_867_, 4, v_diag_857_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_st_ref_put(v___y_831_, v___x_863_);
v___x_865_ = lean_box(0);
v___x_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_873_, lean_object* v_s_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_s_boxed_878_; lean_object* v_res_879_; 
v_s_boxed_878_ = lean_unbox(v_s_874_);
v_res_879_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_873_, v_s_boxed_878_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec(v___y_875_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; lean_object* v___x_887_; 
v___x_886_ = 0;
v___x_887_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_880_, v___x_886_, v___y_882_, v___y_884_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_895_, lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_toCold_902_; lean_object* v_options_903_; lean_object* v_currRecDepth_904_; lean_object* v_maxRecDepth_905_; lean_object* v_ref_906_; lean_object* v_currNamespace_907_; lean_object* v_openDecls_908_; lean_object* v_initHeartbeats_909_; lean_object* v_maxHeartbeats_910_; lean_object* v_currMacroScope_911_; uint8_t v_diag_912_; uint8_t v_suppressElabErrors_913_; lean_object* v_ref_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_toCold_902_ = lean_ctor_get(v___y_899_, 0);
v_options_903_ = lean_ctor_get(v___y_899_, 1);
v_currRecDepth_904_ = lean_ctor_get(v___y_899_, 2);
v_maxRecDepth_905_ = lean_ctor_get(v___y_899_, 3);
v_ref_906_ = lean_ctor_get(v___y_899_, 4);
v_currNamespace_907_ = lean_ctor_get(v___y_899_, 5);
v_openDecls_908_ = lean_ctor_get(v___y_899_, 6);
v_initHeartbeats_909_ = lean_ctor_get(v___y_899_, 7);
v_maxHeartbeats_910_ = lean_ctor_get(v___y_899_, 8);
v_currMacroScope_911_ = lean_ctor_get(v___y_899_, 9);
v_diag_912_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*10);
v_suppressElabErrors_913_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*10 + 1);
v_ref_914_ = l_Lean_replaceRef(v_ref_895_, v_ref_906_);
lean_inc(v_currMacroScope_911_);
lean_inc(v_maxHeartbeats_910_);
lean_inc(v_initHeartbeats_909_);
lean_inc(v_openDecls_908_);
lean_inc(v_currNamespace_907_);
lean_inc(v_maxRecDepth_905_);
lean_inc(v_currRecDepth_904_);
lean_inc_ref(v_options_903_);
lean_inc_ref(v_toCold_902_);
v___x_915_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_915_, 0, v_toCold_902_);
lean_ctor_set(v___x_915_, 1, v_options_903_);
lean_ctor_set(v___x_915_, 2, v_currRecDepth_904_);
lean_ctor_set(v___x_915_, 3, v_maxRecDepth_905_);
lean_ctor_set(v___x_915_, 4, v_ref_914_);
lean_ctor_set(v___x_915_, 5, v_currNamespace_907_);
lean_ctor_set(v___x_915_, 6, v_openDecls_908_);
lean_ctor_set(v___x_915_, 7, v_initHeartbeats_909_);
lean_ctor_set(v___x_915_, 8, v_maxHeartbeats_910_);
lean_ctor_set(v___x_915_, 9, v_currMacroScope_911_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*10, v_diag_912_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*10 + 1, v_suppressElabErrors_913_);
v___x_916_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_896_, v___y_897_, v___y_898_, v___x_915_, v___y_900_);
lean_dec_ref_known(v___x_915_, 10);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_917_, lean_object* v_msg_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_917_, v_msg_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v_ref_917_);
return v_res_924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_925_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
lean_ctor_set(v___x_930_, 3, v___x_929_);
lean_ctor_set(v___x_930_, 4, v___x_928_);
lean_ctor_set(v___x_930_, 5, v___x_928_);
lean_ctor_set(v___x_930_, 6, v___x_928_);
lean_ctor_set(v___x_930_, 7, v___x_928_);
lean_ctor_set(v___x_930_, 8, v___x_928_);
lean_ctor_set(v___x_930_, 9, v___x_928_);
lean_ctor_set(v___x_930_, 10, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(32u);
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_931_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_934_ = ((size_t)5ULL);
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = lean_unsigned_to_nat(32u);
v___x_937_ = lean_mk_empty_array_with_capacity(v___x_936_);
v___x_938_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
lean_ctor_set(v___x_939_, 2, v___x_935_);
lean_ctor_set(v___x_939_, 3, v___x_935_);
lean_ctor_set_usize(v___x_939_, 4, v___x_934_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_940_ = lean_box(1);
v___x_941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_940_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_965_, lean_object* v_declHint_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; lean_object* v_env_970_; uint8_t v___x_971_; 
v___x_969_ = lean_st_ref_get(v___y_967_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = l_Lean_Name_isAnonymous(v_declHint_966_);
if (v___x_971_ == 0)
{
uint8_t v_isExporting_972_; 
v_isExporting_972_ = lean_ctor_get_uint8(v_env_970_, sizeof(void*)*8);
if (v_isExporting_972_ == 0)
{
lean_object* v___x_973_; 
lean_dec_ref(v_env_970_);
lean_dec(v_declHint_966_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v_msg_965_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; uint8_t v___x_975_; 
lean_inc_ref(v_env_970_);
v___x_974_ = l_Lean_Environment_setExporting(v_env_970_, v___x_971_);
lean_inc(v_declHint_966_);
lean_inc_ref(v___x_974_);
v___x_975_ = l_Lean_Environment_contains(v___x_974_, v_declHint_966_, v_isExporting_972_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v_env_970_);
lean_dec(v_declHint_966_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v_msg_965_);
return v___x_976_;
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_c_982_; lean_object* v___x_983_; 
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_979_ = l_Lean_Options_empty;
v___x_980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_980_, 0, v___x_974_);
lean_ctor_set(v___x_980_, 1, v___x_977_);
lean_ctor_set(v___x_980_, 2, v___x_978_);
lean_ctor_set(v___x_980_, 3, v___x_979_);
lean_inc(v_declHint_966_);
v___x_981_ = l_Lean_MessageData_ofConstName(v_declHint_966_, v___x_971_);
v_c_982_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_982_, 0, v___x_980_);
lean_ctor_set(v_c_982_, 1, v___x_981_);
v___x_983_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_970_, v_declHint_966_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref(v_env_970_);
lean_dec(v_declHint_966_);
v___x_984_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_c_982_);
v___x_986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = l_Lean_MessageData_note(v___x_987_);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v_msg_965_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1026_; 
v_val_991_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_993_ = v___x_983_;
v_isShared_994_ = v_isSharedCheck_1026_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_dec(v___x_983_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1026_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_mod_998_; uint8_t v___x_999_; 
v___x_995_ = lean_box(0);
v___x_996_ = l_Lean_Environment_header(v_env_970_);
lean_dec_ref(v_env_970_);
v___x_997_ = l_Lean_EnvironmentHeader_moduleNames(v___x_996_);
v_mod_998_ = lean_array_get(v___x_995_, v___x_997_, v_val_991_);
lean_dec(v_val_991_);
lean_dec_ref(v___x_997_);
v___x_999_ = l_Lean_isPrivateName(v_declHint_966_);
lean_dec(v_declHint_966_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_c_982_);
v___x_1002_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_MessageData_ofName(v_mod_998_);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_MessageData_note(v___x_1007_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v_msg_965_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 0);
lean_ctor_set(v___x_993_, 0, v___x_1009_);
v___x_1011_ = v___x_993_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v_c_982_);
v___x_1015_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_MessageData_ofName(v_mod_998_);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_note(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v_msg_965_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 0);
lean_ctor_set(v___x_993_, 0, v___x_1022_);
v___x_1024_ = v___x_993_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1027_; 
lean_dec_ref(v_env_970_);
lean_dec(v_declHint_966_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v_msg_965_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1028_, lean_object* v_declHint_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1028_, v_declHint_1029_, v___y_1030_);
lean_dec(v___y_1030_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1033_, lean_object* v_declHint_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1050_; 
v___x_1040_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1033_, v_declHint_1034_, v___y_1038_);
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1050_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = l_Lean_unknownIdentifierMessageTag;
v___x_1046_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v_a_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1046_);
v___x_1048_ = v___x_1043_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1051_, lean_object* v_declHint_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1051_, v_declHint_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1059_, lean_object* v_msg_1060_, lean_object* v_declHint_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v_a_1068_; lean_object* v___x_1069_; 
v___x_1067_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1060_, v_declHint_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1059_, v_a_1068_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1070_, lean_object* v_msg_1071_, lean_object* v_declHint_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1070_, v_msg_1071_, v_declHint_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_ref_1070_);
return v_res_1078_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1085_, lean_object* v_constName_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1092_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1093_ = 0;
lean_inc(v_constName_1086_);
v___x_1094_ = l_Lean_MessageData_ofConstName(v_constName_1086_, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1085_, v___x_1097_, v_constName_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1099_, lean_object* v_constName_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1099_, v_constName_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v_ref_1099_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_ref_1113_; lean_object* v___x_1114_; 
v_ref_1113_ = lean_ctor_get(v___y_1110_, 4);
v___x_1114_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1113_, v_constName_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_env_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_st_ref_get(v___y_1126_);
v_env_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_env_1129_);
lean_dec(v___x_1128_);
v___x_1130_ = 0;
lean_inc(v_constName_1122_);
v___x_1131_ = l_Lean_Environment_find_x3f(v_env_1129_, v_constName_1122_, v___x_1130_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1132_;
}
else
{
lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_constName_1122_);
v_val_1133_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1131_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_dec(v___x_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set_tag(v___x_1135_, 0);
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_val_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1153_ = l_Lean_stringToMessageData(v___x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1157_, lean_object* v_nParams_1158_, lean_object* v_belowName_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
lean_inc(v_recName_1157_);
v___x_1165_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1157_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
if (lean_obj_tag(v_a_1166_) == 7)
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1283_; 
v_val_1167_ = lean_ctor_get(v_a_1166_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1166_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1169_ = v_a_1166_;
v_isShared_1170_ = v_isSharedCheck_1283_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_a_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1283_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_toConstantVal_1171_; lean_object* v_numMotives_1172_; lean_object* v_numMinors_1173_; lean_object* v_levelParams_1174_; lean_object* v_type_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_toConstantVal_1171_ = lean_ctor_get(v_val_1167_, 0);
lean_inc_ref(v_toConstantVal_1171_);
v_numMotives_1172_ = lean_ctor_get(v_val_1167_, 4);
lean_inc(v_numMotives_1172_);
v_numMinors_1173_ = lean_ctor_get(v_val_1167_, 5);
lean_inc(v_numMinors_1173_);
lean_dec_ref(v_val_1167_);
v_levelParams_1174_ = lean_ctor_get(v_toConstantVal_1171_, 1);
lean_inc_n(v_levelParams_1174_, 2);
v_type_1175_ = lean_ctor_get(v_toConstantVal_1171_, 2);
lean_inc_ref(v_type_1175_);
lean_dec_ref(v_toConstantVal_1171_);
v___x_1176_ = lean_box(0);
v___x_1177_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1174_, v___x_1176_);
if (lean_obj_tag(v___x_1177_) == 1)
{
lean_object* v_head_1178_; lean_object* v_tail_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v_head_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_head_1178_);
v_tail_1179_ = lean_ctor_get(v___x_1177_, 1);
lean_inc(v_tail_1179_);
lean_dec_ref_known(v___x_1177_, 2);
v___x_1180_ = l_Lean_instInhabitedExpr;
v___f_1181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1181_, 0, v_nParams_1158_);
lean_closure_set(v___f_1181_, 1, v_numMotives_1172_);
lean_closure_set(v___f_1181_, 2, v_numMinors_1173_);
lean_closure_set(v___f_1181_, 3, v___x_1180_);
lean_closure_set(v___f_1181_, 4, v_head_1178_);
lean_closure_set(v___f_1181_, 5, v_tail_1179_);
lean_closure_set(v___f_1181_, 6, v_recName_1157_);
lean_closure_set(v___f_1181_, 7, v_belowName_1159_);
lean_closure_set(v___f_1181_, 8, v_levelParams_1174_);
v___x_1182_ = 0;
v___x_1183_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1175_, v___f_1181_, v___x_1182_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_n(v_a_1184_, 2);
lean_dec_ref_known(v___x_1183_, 1);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 1);
lean_ctor_set(v___x_1169_, 0, v_a_1184_);
v___x_1186_ = v___x_1169_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1184_);
v___x_1186_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_addDecl(v___x_1186_, v___x_1182_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_toConstantVal_1188_; lean_object* v_name_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref_known(v___x_1187_, 1);
v_toConstantVal_1188_ = lean_ctor_get(v_a_1184_, 0);
lean_inc_ref(v_toConstantVal_1188_);
lean_dec(v_a_1184_);
v_name_1189_ = lean_ctor_get(v_toConstantVal_1188_, 0);
lean_inc_n(v_name_1189_, 2);
lean_dec_ref(v_toConstantVal_1188_);
v___x_1190_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1189_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1190_, 0);
lean_dec(v_unused_1267_);
v___x_1192_ = v___x_1190_;
v_isShared_1193_ = v_isSharedCheck_1266_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v___x_1190_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1266_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v_env_1195_; lean_object* v_nextMacroScope_1196_; lean_object* v_ngen_1197_; lean_object* v_auxDeclNGen_1198_; lean_object* v_traceState_1199_; lean_object* v_messages_1200_; lean_object* v_infoState_1201_; lean_object* v_snapshotTasks_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1264_; 
v___x_1194_ = lean_st_ref_take(v_a_1163_);
v_env_1195_ = lean_ctor_get(v___x_1194_, 0);
v_nextMacroScope_1196_ = lean_ctor_get(v___x_1194_, 1);
v_ngen_1197_ = lean_ctor_get(v___x_1194_, 2);
v_auxDeclNGen_1198_ = lean_ctor_get(v___x_1194_, 3);
v_traceState_1199_ = lean_ctor_get(v___x_1194_, 4);
v_messages_1200_ = lean_ctor_get(v___x_1194_, 6);
v_infoState_1201_ = lean_ctor_get(v___x_1194_, 7);
v_snapshotTasks_1202_ = lean_ctor_get(v___x_1194_, 8);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1194_, 5);
lean_dec(v_unused_1265_);
v___x_1204_ = v___x_1194_;
v_isShared_1205_ = v_isSharedCheck_1264_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_snapshotTasks_1202_);
lean_inc(v_infoState_1201_);
lean_inc(v_messages_1200_);
lean_inc(v_traceState_1199_);
lean_inc(v_auxDeclNGen_1198_);
lean_inc(v_ngen_1197_);
lean_inc(v_nextMacroScope_1196_);
lean_inc(v_env_1195_);
lean_dec(v___x_1194_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1264_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_inc(v_name_1189_);
v___x_1206_ = l_Lean_markAuxRecursor(v_env_1195_, v_name_1189_);
v___x_1207_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 5, v___x_1207_);
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1196_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1197_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1198_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1199_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_messages_1200_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_infoState_1201_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_snapshotTasks_1202_);
v___x_1209_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_mctx_1212_; lean_object* v_zetaDeltaFVarIds_1213_; lean_object* v_postponed_1214_; lean_object* v_diag_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1261_; 
v___x_1210_ = lean_st_ref_put(v_a_1163_, v___x_1209_);
v___x_1211_ = lean_st_ref_take(v_a_1161_);
v_mctx_1212_ = lean_ctor_get(v___x_1211_, 0);
v_zetaDeltaFVarIds_1213_ = lean_ctor_get(v___x_1211_, 2);
v_postponed_1214_ = lean_ctor_get(v___x_1211_, 3);
v_diag_1215_ = lean_ctor_get(v___x_1211_, 4);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1211_, 1);
lean_dec(v_unused_1262_);
v___x_1217_ = v___x_1211_;
v_isShared_1218_ = v_isSharedCheck_1261_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_diag_1215_);
lean_inc(v_postponed_1214_);
lean_inc(v_zetaDeltaFVarIds_1213_);
lean_inc(v_mctx_1212_);
lean_dec(v___x_1211_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1261_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_mctx_1212_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_zetaDeltaFVarIds_1213_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_postponed_1214_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_diag_1215_);
v___x_1221_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_env_1224_; lean_object* v_nextMacroScope_1225_; lean_object* v_ngen_1226_; lean_object* v_auxDeclNGen_1227_; lean_object* v_traceState_1228_; lean_object* v_messages_1229_; lean_object* v_infoState_1230_; lean_object* v_snapshotTasks_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1258_; 
v___x_1222_ = lean_st_ref_put(v_a_1161_, v___x_1221_);
v___x_1223_ = lean_st_ref_take(v_a_1163_);
v_env_1224_ = lean_ctor_get(v___x_1223_, 0);
v_nextMacroScope_1225_ = lean_ctor_get(v___x_1223_, 1);
v_ngen_1226_ = lean_ctor_get(v___x_1223_, 2);
v_auxDeclNGen_1227_ = lean_ctor_get(v___x_1223_, 3);
v_traceState_1228_ = lean_ctor_get(v___x_1223_, 4);
v_messages_1229_ = lean_ctor_get(v___x_1223_, 6);
v_infoState_1230_ = lean_ctor_get(v___x_1223_, 7);
v_snapshotTasks_1231_ = lean_ctor_get(v___x_1223_, 8);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1223_, 5);
lean_dec(v_unused_1259_);
v___x_1233_ = v___x_1223_;
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_snapshotTasks_1231_);
lean_inc(v_infoState_1230_);
lean_inc(v_messages_1229_);
lean_inc(v_traceState_1228_);
lean_inc(v_auxDeclNGen_1227_);
lean_inc(v_ngen_1226_);
lean_inc(v_nextMacroScope_1225_);
lean_inc(v_env_1224_);
lean_dec(v___x_1223_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_addProtected(v_env_1224_, v_name_1189_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 5, v___x_1207_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1225_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1226_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1227_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1228_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1229_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_infoState_1230_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1231_);
v___x_1237_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_zetaDeltaFVarIds_1241_; lean_object* v_postponed_1242_; lean_object* v_diag_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v___x_1238_ = lean_st_ref_put(v_a_1163_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v_a_1161_);
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
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1219_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1243_);
v___x_1248_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1249_ = lean_st_ref_put(v_a_1161_, v___x_1248_);
v___x_1250_ = lean_box(0);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1250_);
v___x_1252_ = v___x_1192_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
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
lean_dec(v_a_1184_);
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1169_);
v_a_1269_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1183_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1183_);
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
lean_dec(v___x_1177_);
lean_dec_ref(v_type_1175_);
lean_dec(v_levelParams_1174_);
lean_dec(v_numMinors_1173_);
lean_dec(v_numMotives_1172_);
lean_del_object(v___x_1169_);
lean_dec(v_belowName_1159_);
lean_dec(v_nParams_1158_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1278_ = l_Lean_MessageData_ofName(v_recName_1157_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1281_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1166_);
lean_dec(v_belowName_1159_);
lean_dec(v_nParams_1158_);
v___x_1284_ = l_Lean_MessageData_ofName(v_recName_1157_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1286_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_belowName_1159_);
lean_dec(v_nParams_1158_);
lean_dec(v_recName_1157_);
v_a_1288_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1165_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1165_);
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
lean_object* v___x_1437_; lean_object* v_traceState_1438_; lean_object* v_traces_1439_; lean_object* v___x_1440_; lean_object* v_traceState_1441_; lean_object* v_env_1442_; lean_object* v_nextMacroScope_1443_; lean_object* v_ngen_1444_; lean_object* v_auxDeclNGen_1445_; lean_object* v_cache_1446_; lean_object* v_messages_1447_; lean_object* v_infoState_1448_; lean_object* v_snapshotTasks_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1468_; 
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
v_messages_1447_ = lean_ctor_get(v___x_1440_, 6);
v_infoState_1448_ = lean_ctor_get(v___x_1440_, 7);
v_snapshotTasks_1449_ = lean_ctor_get(v___x_1440_, 8);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1451_ = v___x_1440_;
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snapshotTasks_1449_);
lean_inc(v_infoState_1448_);
lean_inc(v_messages_1447_);
lean_inc(v_cache_1446_);
lean_inc(v_traceState_1441_);
lean_inc(v_auxDeclNGen_1445_);
lean_inc(v_ngen_1444_);
lean_inc(v_nextMacroScope_1443_);
lean_inc(v_env_1442_);
lean_dec(v___x_1440_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1468_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
uint64_t v_tid_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1466_; 
v_tid_1453_ = lean_ctor_get_uint64(v_traceState_1441_, sizeof(void*)*1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_traceState_1441_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_traceState_1441_, 0);
lean_dec(v_unused_1467_);
v___x_1455_ = v_traceState_1441_;
v_isShared_1456_ = v_isSharedCheck_1466_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_traceState_1441_);
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
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_env_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1443_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1445_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v_cache_1446_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_messages_1447_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_infoState_1448_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_snapshotTasks_1449_);
v___x_1461_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_st_ref_put(v___y_1435_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_traces_1439_);
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
lean_object* v_toCold_1580_; lean_object* v_options_1581_; lean_object* v_currRecDepth_1582_; lean_object* v_maxRecDepth_1583_; lean_object* v_ref_1584_; lean_object* v_currNamespace_1585_; lean_object* v_openDecls_1586_; lean_object* v_initHeartbeats_1587_; lean_object* v_maxHeartbeats_1588_; lean_object* v_currMacroScope_1589_; uint8_t v_diag_1590_; uint8_t v_suppressElabErrors_1591_; lean_object* v___x_1592_; lean_object* v_traceState_1593_; lean_object* v_traces_1594_; lean_object* v_ref_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v_msg_1601_; lean_object* v___x_1602_; lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1640_; 
v_toCold_1580_ = lean_ctor_get(v___y_1577_, 0);
v_options_1581_ = lean_ctor_get(v___y_1577_, 1);
v_currRecDepth_1582_ = lean_ctor_get(v___y_1577_, 2);
v_maxRecDepth_1583_ = lean_ctor_get(v___y_1577_, 3);
v_ref_1584_ = lean_ctor_get(v___y_1577_, 4);
v_currNamespace_1585_ = lean_ctor_get(v___y_1577_, 5);
v_openDecls_1586_ = lean_ctor_get(v___y_1577_, 6);
v_initHeartbeats_1587_ = lean_ctor_get(v___y_1577_, 7);
v_maxHeartbeats_1588_ = lean_ctor_get(v___y_1577_, 8);
v_currMacroScope_1589_ = lean_ctor_get(v___y_1577_, 9);
v_diag_1590_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*10);
v_suppressElabErrors_1591_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*10 + 1);
v___x_1592_ = lean_st_ref_get(v___y_1578_);
v_traceState_1593_ = lean_ctor_get(v___x_1592_, 4);
lean_inc_ref(v_traceState_1593_);
lean_dec(v___x_1592_);
v_traces_1594_ = lean_ctor_get(v_traceState_1593_, 0);
lean_inc_ref(v_traces_1594_);
lean_dec_ref(v_traceState_1593_);
v_ref_1595_ = l_Lean_replaceRef(v_ref_1573_, v_ref_1584_);
lean_inc(v_currMacroScope_1589_);
lean_inc(v_maxHeartbeats_1588_);
lean_inc(v_initHeartbeats_1587_);
lean_inc(v_openDecls_1586_);
lean_inc(v_currNamespace_1585_);
lean_inc(v_maxRecDepth_1583_);
lean_inc(v_currRecDepth_1582_);
lean_inc_ref(v_options_1581_);
lean_inc_ref(v_toCold_1580_);
v___x_1596_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1596_, 0, v_toCold_1580_);
lean_ctor_set(v___x_1596_, 1, v_options_1581_);
lean_ctor_set(v___x_1596_, 2, v_currRecDepth_1582_);
lean_ctor_set(v___x_1596_, 3, v_maxRecDepth_1583_);
lean_ctor_set(v___x_1596_, 4, v_ref_1595_);
lean_ctor_set(v___x_1596_, 5, v_currNamespace_1585_);
lean_ctor_set(v___x_1596_, 6, v_openDecls_1586_);
lean_ctor_set(v___x_1596_, 7, v_initHeartbeats_1587_);
lean_ctor_set(v___x_1596_, 8, v_maxHeartbeats_1588_);
lean_ctor_set(v___x_1596_, 9, v_currMacroScope_1589_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*10, v_diag_1590_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*10 + 1, v_suppressElabErrors_1591_);
v___x_1597_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1594_);
lean_dec_ref(v_traces_1594_);
v_sz_1598_ = lean_array_size(v___x_1597_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1598_, v___x_1599_, v___x_1597_);
v_msg_1601_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1601_, 0, v_data_1572_);
lean_ctor_set(v_msg_1601_, 1, v_msg_1574_);
lean_ctor_set(v_msg_1601_, 2, v___x_1600_);
v___x_1602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1601_, v___y_1575_, v___y_1576_, v___x_1596_, v___y_1578_);
lean_dec_ref_known(v___x_1596_, 10);
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1640_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1640_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v_traceState_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_cache_1613_; lean_object* v_messages_1614_; lean_object* v_infoState_1615_; lean_object* v_snapshotTasks_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1639_; 
v___x_1607_ = lean_st_ref_take(v___y_1578_);
v_traceState_1608_ = lean_ctor_get(v___x_1607_, 4);
v_env_1609_ = lean_ctor_get(v___x_1607_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1607_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1607_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1607_, 3);
v_cache_1613_ = lean_ctor_get(v___x_1607_, 5);
v_messages_1614_ = lean_ctor_get(v___x_1607_, 6);
v_infoState_1615_ = lean_ctor_get(v___x_1607_, 7);
v_snapshotTasks_1616_ = lean_ctor_get(v___x_1607_, 8);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1618_ = v___x_1607_;
v_isShared_1619_ = v_isSharedCheck_1639_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snapshotTasks_1616_);
lean_inc(v_infoState_1615_);
lean_inc(v_messages_1614_);
lean_inc(v_cache_1613_);
lean_inc(v_traceState_1608_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1607_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1639_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
uint64_t v_tid_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1637_; 
v_tid_1620_ = lean_ctor_get_uint64(v_traceState_1608_, sizeof(void*)*1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_traceState_1608_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_traceState_1608_, 0);
lean_dec(v_unused_1638_);
v___x_1622_ = v_traceState_1608_;
v_isShared_1623_ = v_isSharedCheck_1637_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_traceState_1608_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1637_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_ref_1573_);
lean_ctor_set(v___x_1624_, 1, v_a_1603_);
v___x_1625_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1571_, v___x_1624_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1625_);
lean_ctor_set_uint64(v_reuseFailAlloc_1636_, sizeof(void*)*1, v_tid_1620_);
v___x_1627_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1629_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 4, v___x_1627_);
v___x_1629_ = v___x_1618_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_env_1609_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1635_, 5, v_cache_1613_);
lean_ctor_set(v_reuseFailAlloc_1635_, 6, v_messages_1614_);
lean_ctor_set(v_reuseFailAlloc_1635_, 7, v_infoState_1615_);
lean_ctor_set(v_reuseFailAlloc_1635_, 8, v_snapshotTasks_1616_);
v___x_1629_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1630_ = lean_st_ref_put(v___y_1578_, v___x_1629_);
v___x_1631_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1631_);
v___x_1633_ = v___x_1605_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1641_, lean_object* v_data_1642_, lean_object* v_ref_1643_, lean_object* v_msg_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1641_, v_data_1642_, v_ref_1643_, v_msg_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1650_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1651_; double v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_float_of_nat(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1656_; double v___x_1657_; 
v___x_1656_ = lean_unsigned_to_nat(1000u);
v___x_1657_ = lean_float_of_nat(v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1658_, uint8_t v_collapsed_1659_, lean_object* v_tag_1660_, lean_object* v_opts_1661_, uint8_t v_clsEnabled_1662_, lean_object* v_oldTraces_1663_, lean_object* v_msg_1664_, lean_object* v_resStartStop_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_fst_1671_; lean_object* v_snd_1672_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v_data_1676_; lean_object* v_fst_1679_; lean_object* v_snd_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___y_1684_; lean_object* v_a_1685_; uint8_t v___y_1700_; double v___y_1731_; 
v_fst_1671_ = lean_ctor_get(v_resStartStop_1665_, 0);
lean_inc(v_fst_1671_);
v_snd_1672_ = lean_ctor_get(v_resStartStop_1665_, 1);
lean_inc(v_snd_1672_);
lean_dec_ref(v_resStartStop_1665_);
v_fst_1679_ = lean_ctor_get(v_snd_1672_, 0);
lean_inc(v_fst_1679_);
v_snd_1680_ = lean_ctor_get(v_snd_1672_, 1);
lean_inc(v_snd_1680_);
lean_dec(v_snd_1672_);
v___x_1681_ = l_Lean_trace_profiler;
v___x_1682_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1661_, v___x_1681_);
if (v___x_1682_ == 0)
{
v___y_1700_ = v___x_1682_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1737_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1661_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; double v___x_1740_; double v___x_1741_; double v___x_1742_; 
v___x_1738_ = l_Lean_trace_profiler_threshold;
v___x_1739_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1661_, v___x_1738_);
v___x_1740_ = lean_float_of_nat(v___x_1739_);
v___x_1741_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1742_ = lean_float_div(v___x_1740_, v___x_1741_);
v___y_1731_ = v___x_1742_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1743_; lean_object* v___x_1744_; double v___x_1745_; 
v___x_1743_ = l_Lean_trace_profiler_threshold;
v___x_1744_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1661_, v___x_1743_);
v___x_1745_ = lean_float_of_nat(v___x_1744_);
v___y_1731_ = v___x_1745_;
goto v___jp_1730_;
}
}
v___jp_1673_:
{
lean_object* v___x_1677_; 
lean_inc(v___y_1674_);
v___x_1677_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1663_, v_data_1676_, v___y_1674_, v___y_1675_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1678_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1671_);
return v___x_1678_;
}
else
{
lean_dec(v_fst_1671_);
return v___x_1677_;
}
}
v___jp_1683_:
{
uint8_t v_result_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; double v___x_1689_; lean_object* v_data_1690_; 
v_result_1686_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1671_);
v___x_1687_ = lean_box(v_result_1686_);
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
v___x_1689_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1660_);
lean_inc_ref(v___x_1688_);
lean_inc(v_cls_1658_);
v_data_1690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1690_, 0, v_cls_1658_);
lean_ctor_set(v_data_1690_, 1, v___x_1688_);
lean_ctor_set(v_data_1690_, 2, v_tag_1660_);
lean_ctor_set_float(v_data_1690_, sizeof(void*)*3, v___x_1689_);
lean_ctor_set_float(v_data_1690_, sizeof(void*)*3 + 8, v___x_1689_);
lean_ctor_set_uint8(v_data_1690_, sizeof(void*)*3 + 16, v_collapsed_1659_);
if (v___x_1682_ == 0)
{
lean_dec_ref_known(v___x_1688_, 1);
lean_dec(v_snd_1680_);
lean_dec(v_fst_1679_);
lean_dec_ref(v_tag_1660_);
lean_dec(v_cls_1658_);
v___y_1674_ = v___y_1684_;
v___y_1675_ = v_a_1685_;
v_data_1676_ = v_data_1690_;
goto v___jp_1673_;
}
else
{
lean_object* v_data_1691_; double v___x_1692_; double v___x_1693_; 
lean_dec_ref_known(v_data_1690_, 3);
v_data_1691_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1691_, 0, v_cls_1658_);
lean_ctor_set(v_data_1691_, 1, v___x_1688_);
lean_ctor_set(v_data_1691_, 2, v_tag_1660_);
v___x_1692_ = lean_unbox_float(v_fst_1679_);
lean_dec(v_fst_1679_);
lean_ctor_set_float(v_data_1691_, sizeof(void*)*3, v___x_1692_);
v___x_1693_ = lean_unbox_float(v_snd_1680_);
lean_dec(v_snd_1680_);
lean_ctor_set_float(v_data_1691_, sizeof(void*)*3 + 8, v___x_1693_);
lean_ctor_set_uint8(v_data_1691_, sizeof(void*)*3 + 16, v_collapsed_1659_);
v___y_1674_ = v___y_1684_;
v___y_1675_ = v_a_1685_;
v_data_1676_ = v_data_1691_;
goto v___jp_1673_;
}
}
v___jp_1694_:
{
lean_object* v_ref_1695_; lean_object* v___x_1696_; 
v_ref_1695_ = lean_ctor_get(v___y_1668_, 4);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
lean_inc(v___y_1667_);
lean_inc_ref(v___y_1666_);
lean_inc(v_fst_1671_);
v___x_1696_ = lean_apply_6(v_msg_1664_, v_fst_1671_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, lean_box(0));
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___y_1684_ = v_ref_1695_;
v_a_1685_ = v_a_1697_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1698_; 
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1684_ = v_ref_1695_;
v_a_1685_ = v___x_1698_;
goto v___jp_1683_;
}
}
v___jp_1699_:
{
if (v_clsEnabled_1662_ == 0)
{
if (v___y_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v_traceState_1702_; lean_object* v_env_1703_; lean_object* v_nextMacroScope_1704_; lean_object* v_ngen_1705_; lean_object* v_auxDeclNGen_1706_; lean_object* v_cache_1707_; lean_object* v_messages_1708_; lean_object* v_infoState_1709_; lean_object* v_snapshotTasks_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1729_; 
lean_dec(v_snd_1680_);
lean_dec(v_fst_1679_);
lean_dec_ref(v_msg_1664_);
lean_dec_ref(v_tag_1660_);
lean_dec(v_cls_1658_);
v___x_1701_ = lean_st_ref_take(v___y_1669_);
v_traceState_1702_ = lean_ctor_get(v___x_1701_, 4);
v_env_1703_ = lean_ctor_get(v___x_1701_, 0);
v_nextMacroScope_1704_ = lean_ctor_get(v___x_1701_, 1);
v_ngen_1705_ = lean_ctor_get(v___x_1701_, 2);
v_auxDeclNGen_1706_ = lean_ctor_get(v___x_1701_, 3);
v_cache_1707_ = lean_ctor_get(v___x_1701_, 5);
v_messages_1708_ = lean_ctor_get(v___x_1701_, 6);
v_infoState_1709_ = lean_ctor_get(v___x_1701_, 7);
v_snapshotTasks_1710_ = lean_ctor_get(v___x_1701_, 8);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1712_ = v___x_1701_;
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_snapshotTasks_1710_);
lean_inc(v_infoState_1709_);
lean_inc(v_messages_1708_);
lean_inc(v_cache_1707_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1706_);
lean_inc(v_ngen_1705_);
lean_inc(v_nextMacroScope_1704_);
lean_inc(v_env_1703_);
lean_dec(v___x_1701_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1729_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
uint64_t v_tid_1714_; lean_object* v_traces_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1728_; 
v_tid_1714_ = lean_ctor_get_uint64(v_traceState_1702_, sizeof(void*)*1);
v_traces_1715_ = lean_ctor_get(v_traceState_1702_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v_traceState_1702_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1717_ = v_traceState_1702_;
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_traces_1715_);
lean_dec(v_traceState_1702_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1728_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1663_, v_traces_1715_);
lean_dec_ref(v_traces_1715_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1719_);
lean_ctor_set_uint64(v_reuseFailAlloc_1727_, sizeof(void*)*1, v_tid_1714_);
v___x_1721_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 4, v___x_1721_);
v___x_1723_ = v___x_1712_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_env_1703_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_nextMacroScope_1704_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_ngen_1705_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_auxDeclNGen_1706_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v___x_1721_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v_cache_1707_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v_messages_1708_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_infoState_1709_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_snapshotTasks_1710_);
v___x_1723_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = lean_st_ref_put(v___y_1669_, v___x_1723_);
v___x_1725_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1671_);
return v___x_1725_;
}
}
}
}
}
else
{
goto v___jp_1694_;
}
}
else
{
goto v___jp_1694_;
}
}
v___jp_1730_:
{
double v___x_1732_; double v___x_1733_; double v___x_1734_; uint8_t v___x_1735_; 
v___x_1732_ = lean_unbox_float(v_snd_1680_);
v___x_1733_ = lean_unbox_float(v_fst_1679_);
v___x_1734_ = lean_float_sub(v___x_1732_, v___x_1733_);
v___x_1735_ = lean_float_decLt(v___y_1731_, v___x_1734_);
v___y_1700_ = v___x_1735_;
goto v___jp_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1746_, lean_object* v_collapsed_1747_, lean_object* v_tag_1748_, lean_object* v_opts_1749_, lean_object* v_clsEnabled_1750_, lean_object* v_oldTraces_1751_, lean_object* v_msg_1752_, lean_object* v_resStartStop_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v_collapsed_boxed_1759_; uint8_t v_clsEnabled_boxed_1760_; lean_object* v_res_1761_; 
v_collapsed_boxed_1759_ = lean_unbox(v_collapsed_1747_);
v_clsEnabled_boxed_1760_ = lean_unbox(v_clsEnabled_1750_);
v_res_1761_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1746_, v_collapsed_boxed_1759_, v_tag_1748_, v_opts_1749_, v_clsEnabled_boxed_1760_, v_oldTraces_1751_, v_msg_1752_, v_resStartStop_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec_ref(v_opts_1749_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1762_, lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v___x_1765_, lean_object* v_a_1766_, lean_object* v_b_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_nat_dec_lt(v_a_1766_, v_upperBound_1762_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec(v_a_1766_);
lean_dec(v___x_1765_);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_b_1767_);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_a_1766_, v___x_1775_);
lean_dec(v_a_1766_);
lean_inc_n(v___x_1776_, 2);
lean_inc(v___x_1763_);
v___x_1777_ = lean_name_append_index_after(v___x_1763_, v___x_1776_);
lean_inc(v___x_1764_);
v___x_1778_ = lean_name_append_index_after(v___x_1764_, v___x_1776_);
lean_inc(v___x_1765_);
v___x_1779_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1777_, v___x_1765_, v___x_1778_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1780_; 
lean_dec_ref_known(v___x_1779_, 1);
v___x_1780_ = lean_box(0);
v_a_1766_ = v___x_1776_;
v_b_1767_ = v___x_1780_;
goto _start;
}
else
{
lean_dec(v___x_1776_);
lean_dec(v___x_1765_);
lean_dec(v___x_1764_);
lean_dec(v___x_1763_);
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1782_, lean_object* v___x_1783_, lean_object* v___x_1784_, lean_object* v___x_1785_, lean_object* v_a_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1782_, v___x_1783_, v___x_1784_, v___x_1785_, v_a_1786_, v_b_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v_upperBound_1782_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1804_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1805_ = l_Lean_Name_append(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1806_; double v___x_1807_; 
v___x_1806_ = lean_unsigned_to_nat(1000000000u);
v___x_1807_ = lean_float_of_nat(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_options_1814_; lean_object* v_toCold_1815_; uint8_t v_hasTrace_1816_; lean_object* v___x_1817_; 
v_options_1814_ = lean_ctor_get(v_a_1811_, 1);
v_toCold_1815_ = lean_ctor_get(v_a_1811_, 0);
v_hasTrace_1816_ = lean_ctor_get_uint8(v_options_1814_, sizeof(void*)*1);
v___x_1817_ = lean_box(0);
if (v_hasTrace_1816_ == 0)
{
lean_object* v___x_1818_; 
lean_inc(v_indName_1808_);
v___x_1818_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1882_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1882_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1882_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
if (lean_obj_tag(v_a_1819_) == 5)
{
lean_object* v_val_1823_; uint8_t v_isRec_1824_; 
v_val_1823_ = lean_ctor_get(v_a_1819_, 0);
lean_inc_ref(v_val_1823_);
lean_dec_ref_known(v_a_1819_, 1);
v_isRec_1824_ = lean_ctor_get_uint8(v_val_1823_, sizeof(void*)*6);
if (v_isRec_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_dec_ref(v_val_1823_);
lean_dec(v_indName_1808_);
v___x_1825_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1825_);
v___x_1827_ = v___x_1821_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
lean_object* v_toConstantVal_1829_; lean_object* v_numParams_1830_; lean_object* v_all_1831_; lean_object* v_numNested_1832_; lean_object* v_type_1833_; lean_object* v___x_1834_; 
lean_del_object(v___x_1821_);
v_toConstantVal_1829_ = lean_ctor_get(v_val_1823_, 0);
lean_inc_ref(v_toConstantVal_1829_);
v_numParams_1830_ = lean_ctor_get(v_val_1823_, 1);
lean_inc(v_numParams_1830_);
v_all_1831_ = lean_ctor_get(v_val_1823_, 3);
lean_inc(v_all_1831_);
v_numNested_1832_ = lean_ctor_get(v_val_1823_, 5);
lean_inc(v_numNested_1832_);
lean_dec_ref(v_val_1823_);
v_type_1833_ = lean_ctor_get(v_toConstantVal_1829_, 2);
lean_inc_ref(v_type_1833_);
lean_dec_ref(v_toConstantVal_1829_);
v___x_1834_ = l_Lean_Meta_isPropFormerType(v_type_1833_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1869_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1869_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1869_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_unbox(v_a_1835_);
lean_dec(v_a_1835_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1837_);
lean_inc_n(v_indName_1808_, 2);
v___x_1840_ = l_Lean_mkRecName(v_indName_1808_);
v___x_1841_ = l_Lean_mkBelowName(v_indName_1808_);
lean_inc(v___x_1841_);
lean_inc(v_numParams_1830_);
lean_inc(v___x_1840_);
v___x_1842_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1840_, v_numParams_1830_, v___x_1841_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1863_; 
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v___x_1842_, 0);
lean_dec(v_unused_1864_);
v___x_1844_ = v___x_1842_;
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v___x_1842_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = lean_unsigned_to_nat(0u);
v___x_1847_ = l_List_get_x21Internal___redArg(v___x_1817_, v_all_1831_, v___x_1846_);
lean_dec(v_all_1831_);
v___x_1848_ = lean_name_eq(v___x_1847_, v_indName_1808_);
lean_dec(v_indName_1808_);
lean_dec(v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v___x_1841_);
lean_dec(v___x_1840_);
lean_dec(v_numNested_1832_);
lean_dec(v_numParams_1830_);
v___x_1849_ = lean_box(0);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1849_);
v___x_1851_ = v___x_1844_;
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
lean_del_object(v___x_1844_);
v___x_1853_ = lean_box(0);
v___x_1854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1832_, v___x_1840_, v___x_1841_, v_numParams_1830_, v___x_1846_, v___x_1853_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_numNested_1832_);
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
lean_dec(v___x_1841_);
lean_dec(v___x_1840_);
lean_dec(v_numNested_1832_);
lean_dec(v_all_1831_);
lean_dec(v_numParams_1830_);
lean_dec(v_indName_1808_);
return v___x_1842_;
}
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_numNested_1832_);
lean_dec(v_all_1831_);
lean_dec(v_numParams_1830_);
lean_dec(v_indName_1808_);
v___x_1865_ = lean_box(0);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1865_);
v___x_1867_ = v___x_1837_;
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
lean_dec(v_numNested_1832_);
lean_dec(v_all_1831_);
lean_dec(v_numParams_1830_);
lean_dec(v_indName_1808_);
v_a_1870_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1834_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1834_);
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
lean_dec(v_a_1819_);
lean_dec(v_indName_1808_);
v___x_1878_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1878_);
v___x_1880_ = v___x_1821_;
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
lean_dec(v_indName_1808_);
v_a_1883_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1818_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1818_);
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
v_inheritedTraceOptions_1891_ = lean_ctor_get(v_toCold_1815_, 4);
lean_inc(v_indName_1808_);
v___f_1892_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1892_, 0, v_indName_1808_);
v___x_1893_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1894_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1895_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1896_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1891_, v_options_1814_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2009_ = l_Lean_trace_profiler;
v___x_2010_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1814_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v___f_1892_);
lean_inc(v_indName_1808_);
v___x_2011_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2075_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2075_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2075_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
if (lean_obj_tag(v_a_2012_) == 5)
{
lean_object* v_val_2016_; uint8_t v_isRec_2017_; 
v_val_2016_ = lean_ctor_get(v_a_2012_, 0);
lean_inc_ref(v_val_2016_);
lean_dec_ref_known(v_a_2012_, 1);
v_isRec_2017_ = lean_ctor_get_uint8(v_val_2016_, sizeof(void*)*6);
if (v_isRec_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec_ref(v_val_2016_);
lean_dec(v_indName_1808_);
v___x_2018_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2018_);
v___x_2020_ = v___x_2014_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
else
{
lean_object* v_toConstantVal_2022_; lean_object* v_numParams_2023_; lean_object* v_all_2024_; lean_object* v_numNested_2025_; lean_object* v_type_2026_; lean_object* v___x_2027_; 
lean_del_object(v___x_2014_);
v_toConstantVal_2022_ = lean_ctor_get(v_val_2016_, 0);
lean_inc_ref(v_toConstantVal_2022_);
v_numParams_2023_ = lean_ctor_get(v_val_2016_, 1);
lean_inc(v_numParams_2023_);
v_all_2024_ = lean_ctor_get(v_val_2016_, 3);
lean_inc(v_all_2024_);
v_numNested_2025_ = lean_ctor_get(v_val_2016_, 5);
lean_inc(v_numNested_2025_);
lean_dec_ref(v_val_2016_);
v_type_2026_ = lean_ctor_get(v_toConstantVal_2022_, 2);
lean_inc_ref(v_type_2026_);
lean_dec_ref(v_toConstantVal_2022_);
v___x_2027_ = l_Lean_Meta_isPropFormerType(v_type_2026_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2062_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2062_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2062_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_del_object(v___x_2030_);
lean_inc_n(v_indName_1808_, 2);
v___x_2033_ = l_Lean_mkRecName(v_indName_1808_);
v___x_2034_ = l_Lean_mkBelowName(v_indName_1808_);
lean_inc(v___x_2034_);
lean_inc(v_numParams_2023_);
lean_inc(v___x_2033_);
v___x_2035_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2033_, v_numParams_2023_, v___x_2034_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2056_; 
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2057_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2056_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2056_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2039_ = lean_unsigned_to_nat(0u);
v___x_2040_ = l_List_get_x21Internal___redArg(v___x_1817_, v_all_2024_, v___x_2039_);
lean_dec(v_all_2024_);
v___x_2041_ = lean_name_eq(v___x_2040_, v_indName_1808_);
lean_dec(v_indName_1808_);
lean_dec(v___x_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec(v___x_2034_);
lean_dec(v___x_2033_);
lean_dec(v_numNested_2025_);
lean_dec(v_numParams_2023_);
v___x_2042_ = lean_box(0);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2042_);
v___x_2044_ = v___x_2037_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_del_object(v___x_2037_);
v___x_2046_ = lean_box(0);
v___x_2047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2025_, v___x_2033_, v___x_2034_, v_numParams_2023_, v___x_2039_, v___x_2046_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_numNested_2025_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2047_, 0);
lean_dec(v_unused_2055_);
v___x_2049_ = v___x_2047_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v___x_2047_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2046_);
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2046_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
return v___x_2047_;
}
}
}
}
else
{
lean_dec(v___x_2034_);
lean_dec(v___x_2033_);
lean_dec(v_numNested_2025_);
lean_dec(v_all_2024_);
lean_dec(v_numParams_2023_);
lean_dec(v_indName_1808_);
return v___x_2035_;
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec(v_numNested_2025_);
lean_dec(v_all_2024_);
lean_dec(v_numParams_2023_);
lean_dec(v_indName_1808_);
v___x_2058_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2058_);
v___x_2060_ = v___x_2030_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec(v_numNested_2025_);
lean_dec(v_all_2024_);
lean_dec(v_numParams_2023_);
lean_dec(v_indName_1808_);
v_a_2063_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2027_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2027_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec(v_a_2012_);
lean_dec(v_indName_1808_);
v___x_2071_ = lean_box(0);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2071_);
v___x_2073_ = v___x_2014_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec(v_indName_1808_);
v_a_2076_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2011_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2011_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
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
v___x_1902_ = lean_float_of_nat(v___y_1898_);
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
v___x_1911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1893_, v_hasTrace_1816_, v___x_1894_, v_options_1814_, v___x_1896_, v___y_1899_, v___f_1892_, v___x_1910_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
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
v___x_1927_ = lean_float_of_nat(v___y_1923_);
v___x_1928_ = lean_float_of_nat(v___x_1926_);
v___x_1929_ = lean_box_float(v___x_1927_);
v___x_1930_ = lean_box_float(v___x_1928_);
v___x_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1925_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1893_, v_hasTrace_1816_, v___x_1894_, v_options_1814_, v___x_1896_, v___y_1924_, v___f_1892_, v___x_1932_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
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
v___x_1945_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1812_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v___x_1947_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1948_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1814_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1808_);
v___x_1950_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
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
lean_dec(v_indName_1808_);
v___x_1954_ = lean_box(0);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
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
v___x_1960_ = l_Lean_Meta_isPropFormerType(v_type_1959_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
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
lean_inc_n(v_indName_1808_, 2);
v___x_1963_ = l_Lean_mkRecName(v_indName_1808_);
v___x_1964_ = l_Lean_mkBelowName(v_indName_1808_);
lean_inc(v___x_1964_);
lean_inc(v_numParams_1956_);
lean_inc(v___x_1963_);
v___x_1965_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1963_, v_numParams_1956_, v___x_1964_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
lean_dec_ref_known(v___x_1965_, 1);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = l_List_get_x21Internal___redArg(v___x_1817_, v_all_1957_, v___x_1966_);
lean_dec(v_all_1957_);
v___x_1968_ = lean_name_eq(v___x_1967_, v_indName_1808_);
lean_dec(v_indName_1808_);
lean_dec(v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec(v___x_1964_);
lean_dec(v___x_1963_);
lean_dec(v_numNested_1958_);
lean_dec(v_numParams_1956_);
v___x_1969_ = lean_box(0);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
v_a_1915_ = v___x_1969_;
goto v___jp_1912_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_box(0);
v___x_1971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1958_, v___x_1963_, v___x_1964_, v_numParams_1956_, v___x_1966_, v___x_1970_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_numNested_1958_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_dec_ref_known(v___x_1971_, 1);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
v_a_1915_ = v___x_1970_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___y_1918_ = v___x_1949_;
v___y_1919_ = v_a_1946_;
v_a_1920_ = v_a_1972_;
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
lean_dec(v_indName_1808_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1973_; 
v_a_1973_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
v_a_1915_ = v_a_1973_;
goto v___jp_1912_;
}
else
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1918_ = v___x_1949_;
v___y_1919_ = v_a_1946_;
v_a_1920_ = v_a_1974_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v___x_1975_; 
lean_dec(v_numNested_1958_);
lean_dec(v_all_1957_);
lean_dec(v_numParams_1956_);
lean_dec(v_indName_1808_);
v___x_1975_ = lean_box(0);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
v_a_1915_ = v___x_1975_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1976_; 
lean_dec(v_numNested_1958_);
lean_dec(v_all_1957_);
lean_dec(v_numParams_1956_);
lean_dec(v_indName_1808_);
v_a_1976_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1960_, 1);
v___y_1918_ = v___x_1949_;
v___y_1919_ = v_a_1946_;
v_a_1920_ = v_a_1976_;
goto v___jp_1917_;
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v_a_1951_);
lean_dec(v_indName_1808_);
v___x_1977_ = lean_box(0);
v___y_1913_ = v___x_1949_;
v___y_1914_ = v_a_1946_;
v_a_1915_ = v___x_1977_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_a_1978_; 
lean_dec(v_indName_1808_);
v_a_1978_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1950_, 1);
v___y_1918_ = v___x_1949_;
v___y_1919_ = v_a_1946_;
v_a_1920_ = v_a_1978_;
goto v___jp_1917_;
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1808_);
v___x_1980_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
if (lean_obj_tag(v_a_1981_) == 5)
{
lean_object* v_val_1982_; uint8_t v_isRec_1983_; 
v_val_1982_ = lean_ctor_get(v_a_1981_, 0);
lean_inc_ref(v_val_1982_);
lean_dec_ref_known(v_a_1981_, 1);
v_isRec_1983_ = lean_ctor_get_uint8(v_val_1982_, sizeof(void*)*6);
if (v_isRec_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v_val_1982_);
lean_dec(v_indName_1808_);
v___x_1984_ = lean_box(0);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v___x_1984_;
goto v___jp_1934_;
}
else
{
lean_object* v_toConstantVal_1985_; lean_object* v_numParams_1986_; lean_object* v_all_1987_; lean_object* v_numNested_1988_; lean_object* v_type_1989_; lean_object* v___x_1990_; 
v_toConstantVal_1985_ = lean_ctor_get(v_val_1982_, 0);
lean_inc_ref(v_toConstantVal_1985_);
v_numParams_1986_ = lean_ctor_get(v_val_1982_, 1);
lean_inc(v_numParams_1986_);
v_all_1987_ = lean_ctor_get(v_val_1982_, 3);
lean_inc(v_all_1987_);
v_numNested_1988_ = lean_ctor_get(v_val_1982_, 5);
lean_inc(v_numNested_1988_);
lean_dec_ref(v_val_1982_);
v_type_1989_ = lean_ctor_get(v_toConstantVal_1985_, 2);
lean_inc_ref(v_type_1989_);
lean_dec_ref(v_toConstantVal_1985_);
v___x_1990_ = l_Lean_Meta_isPropFormerType(v_type_1989_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; uint8_t v___x_1992_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v___x_1992_ = lean_unbox(v_a_1991_);
lean_dec(v_a_1991_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_inc_n(v_indName_1808_, 2);
v___x_1993_ = l_Lean_mkRecName(v_indName_1808_);
v___x_1994_ = l_Lean_mkBelowName(v_indName_1808_);
lean_inc(v___x_1994_);
lean_inc(v_numParams_1986_);
lean_inc(v___x_1993_);
v___x_1995_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1993_, v_numParams_1986_, v___x_1994_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
lean_dec_ref_known(v___x_1995_, 1);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = l_List_get_x21Internal___redArg(v___x_1817_, v_all_1987_, v___x_1996_);
lean_dec(v_all_1987_);
v___x_1998_ = lean_name_eq(v___x_1997_, v_indName_1808_);
lean_dec(v_indName_1808_);
lean_dec(v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
lean_dec(v___x_1994_);
lean_dec(v___x_1993_);
lean_dec(v_numNested_1988_);
lean_dec(v_numParams_1986_);
v___x_1999_ = lean_box(0);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v___x_1999_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1988_, v___x_1993_, v___x_1994_, v_numParams_1986_, v___x_1996_, v___x_2000_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_);
lean_dec(v_numNested_1988_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_dec_ref_known(v___x_2001_, 1);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v___x_2000_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___y_1940_ = v___x_1979_;
v___y_1941_ = v_a_1946_;
v_a_1942_ = v_a_2002_;
goto v___jp_1939_;
}
}
}
else
{
lean_dec(v___x_1994_);
lean_dec(v___x_1993_);
lean_dec(v_numNested_1988_);
lean_dec(v_all_1987_);
lean_dec(v_numParams_1986_);
lean_dec(v_indName_1808_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1995_, 1);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v_a_2003_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_2004_; 
v_a_2004_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_1995_, 1);
v___y_1940_ = v___x_1979_;
v___y_1941_ = v_a_1946_;
v_a_1942_ = v_a_2004_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_2005_; 
lean_dec(v_numNested_1988_);
lean_dec(v_all_1987_);
lean_dec(v_numParams_1986_);
lean_dec(v_indName_1808_);
v___x_2005_ = lean_box(0);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v___x_2005_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_2006_; 
lean_dec(v_numNested_1988_);
lean_dec(v_all_1987_);
lean_dec(v_numParams_1986_);
lean_dec(v_indName_1808_);
v_a_2006_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1940_ = v___x_1979_;
v___y_1941_ = v_a_1946_;
v_a_1942_ = v_a_2006_;
goto v___jp_1939_;
}
}
}
else
{
lean_object* v___x_2007_; 
lean_dec(v_a_1981_);
lean_dec(v_indName_1808_);
v___x_2007_ = lean_box(0);
v___y_1935_ = v___x_1979_;
v___y_1936_ = v_a_1946_;
v_a_1937_ = v___x_2007_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_2008_; 
lean_dec(v_indName_1808_);
v_a_2008_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_1980_, 1);
v___y_1940_ = v___x_1979_;
v___y_1941_ = v_a_1946_;
v_a_1942_ = v_a_2008_;
goto v___jp_1939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_mkBelow(v_indName_2084_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2091_, lean_object* v___x_2092_, lean_object* v___x_2093_, lean_object* v___x_2094_, lean_object* v_inst_2095_, lean_object* v_R_2096_, lean_object* v_a_2097_, lean_object* v_b_2098_, lean_object* v_c_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2091_, v___x_2092_, v___x_2093_, v___x_2094_, v_a_2097_, v_b_2098_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v___x_2109_, lean_object* v_inst_2110_, lean_object* v_R_2111_, lean_object* v_a_2112_, lean_object* v_b_2113_, lean_object* v_c_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2106_, v___x_2107_, v___x_2108_, v___x_2109_, v_inst_2110_, v_R_2111_, v_a_2112_, v_b_2113_, v_c_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v_upperBound_2106_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2122_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2129_, v_x_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
if (lean_obj_tag(v_a_2137_) == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = l_List_reverse___redArg(v_a_2138_);
return v___x_2139_;
}
else
{
lean_object* v_head_2140_; lean_object* v_tail_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2150_; 
v_head_2140_ = lean_ctor_get(v_a_2137_, 0);
v_tail_2141_ = lean_ctor_get(v_a_2137_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_a_2137_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2143_ = v_a_2137_;
v_isShared_2144_ = v_isSharedCheck_2150_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_tail_2141_);
lean_inc(v_head_2140_);
lean_dec(v_a_2137_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2150_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2145_ = l_Lean_MessageData_ofExpr(v_head_2140_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 1, v_a_2138_);
lean_ctor_set(v___x_2143_, 0, v___x_2145_);
v___x_2147_ = v___x_2143_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2138_);
v___x_2147_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_a_2137_ = v_tail_2141_;
v_a_2138_ = v___x_2147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2151_, lean_object* v_v_2152_, lean_object* v_i_2153_){
_start:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_array_get_size(v_xs_2151_);
v___x_2155_ = lean_nat_dec_lt(v_i_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; 
lean_dec(v_i_2153_);
v___x_2156_ = lean_box(0);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = lean_array_fget_borrowed(v_xs_2151_, v_i_2153_);
v___x_2158_ = lean_expr_eqv(v___x_2157_, v_v_2152_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v_i_2153_, v___x_2159_);
lean_dec(v_i_2153_);
v_i_2153_ = v___x_2160_;
goto _start;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2162_, 0, v_i_2153_);
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2163_, lean_object* v_v_2164_, lean_object* v_i_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2163_, v_v_2164_, v_i_2165_);
lean_dec_ref(v_v_2164_);
lean_dec_ref(v_xs_2163_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2167_, lean_object* v_v_2168_){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2167_, v_v_2168_, v___x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2171_, lean_object* v_v_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2171_, v_v_2172_);
lean_dec_ref(v_v_2172_);
lean_dec_ref(v_xs_2171_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2174_, lean_object* v_v_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2174_, v_v_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v___x_2177_; 
v___x_2177_ = lean_box(0);
return v___x_2177_;
}
else
{
lean_object* v_val_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_val_2178_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2176_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_val_2178_);
lean_dec(v___x_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_val_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2186_, lean_object* v_v_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2186_, v_v_2187_);
lean_dec_ref(v_v_2187_);
lean_dec_ref(v_xs_2186_);
return v_res_2188_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2191_ = l_Lean_stringToMessageData(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2195_, lean_object* v_prods_2196_, lean_object* v_motives_2197_, lean_object* v_fs_2198_, lean_object* v_minor__type_2199_, lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
if (lean_obj_tag(v_x_2200_) == 5)
{
lean_object* v_fn_2208_; lean_object* v_arg_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_fn_2208_ = lean_ctor_get(v_x_2200_, 0);
lean_inc_ref(v_fn_2208_);
v_arg_2209_ = lean_ctor_get(v_x_2200_, 1);
lean_inc_ref(v_arg_2209_);
lean_dec_ref_known(v_x_2200_, 2);
v___x_2210_ = lean_array_set(v_x_2201_, v_x_2202_, v_arg_2209_);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_sub(v_x_2202_, v___x_2211_);
lean_dec(v_x_2202_);
v_x_2200_ = v_fn_2208_;
v_x_2201_ = v___x_2210_;
v_x_2202_ = v___x_2212_;
goto _start;
}
else
{
lean_object* v___x_2214_; 
lean_dec(v_x_2202_);
v___x_2214_ = l_Lean_Meta_PProdN_mk(v_rlvl_2195_, v_prods_2196_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2197_, v_x_2200_);
lean_dec_ref(v_x_2200_);
if (lean_obj_tag(v___x_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec_ref(v_minor__type_2199_);
lean_dec_ref(v_motives_2197_);
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = l_Lean_instInhabitedExpr;
v___x_2219_ = lean_array_get_borrowed(v___x_2218_, v_fs_2198_, v_val_2217_);
lean_dec(v_val_2217_);
lean_inc(v_a_2215_);
v___x_2220_ = lean_array_push(v_x_2201_, v_a_2215_);
lean_inc(v___x_2219_);
v___x_2221_ = l_Lean_mkAppN(v___x_2219_, v___x_2220_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = l_Lean_Meta_mkPProdMk(v___x_2221_, v_a_2215_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v___x_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_x_2201_);
v___x_2223_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2224_ = l_Lean_MessageData_ofExpr(v_minor__type_2199_);
v___x_2225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2223_);
lean_ctor_set(v___x_2225_, 1, v___x_2224_);
v___x_2226_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2225_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = lean_array_to_list(v_motives_2197_);
v___x_2229_ = lean_box(0);
v___x_2230_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2228_, v___x_2229_);
v___x_2231_ = l_Lean_MessageData_ofList(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2227_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2232_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2233_;
}
}
else
{
lean_dec_ref(v_x_2201_);
lean_dec_ref(v_x_2200_);
lean_dec_ref(v_minor__type_2199_);
lean_dec_ref(v_motives_2197_);
return v___x_2214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2234_, lean_object* v_prods_2235_, lean_object* v_motives_2236_, lean_object* v_fs_2237_, lean_object* v_minor__type_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2234_, v_prods_2235_, v_motives_2236_, v_fs_2237_, v_minor__type_2238_, v_x_2239_, v_x_2240_, v_x_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_fs_2237_);
return v_res_2247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2248_; lean_object* v_dummy_2249_; 
v___x_2248_ = lean_box(0);
v_dummy_2249_ = l_Lean_Expr_sort___override(v___x_2248_);
return v_dummy_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2250_, lean_object* v_head_2251_, lean_object* v_belows_2252_, lean_object* v_prods_2253_, lean_object* v_rlvl_2254_, lean_object* v_fs_2255_, lean_object* v_minor__type_2256_, lean_object* v_tail_2257_, lean_object* v_arg__args_2258_, lean_object* v_arg__type_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2250_, v_head_2251_, v_belows_2252_, v_prods_2253_, v_rlvl_2254_, v_fs_2255_, v_minor__type_2256_, v_tail_2257_, v_arg__args_2258_, v_arg__type_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_arg__args_2258_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2266_, lean_object* v_motives_2267_, lean_object* v_belows_2268_, lean_object* v_fs_2269_, lean_object* v_minor__type_2270_, lean_object* v_prods_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
if (lean_obj_tag(v_a_2272_) == 0)
{
lean_object* v_dummy_2278_; lean_object* v_nargs_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec_ref(v_belows_2268_);
v_dummy_2278_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2279_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2270_);
lean_inc(v_nargs_2279_);
v___x_2280_ = lean_mk_array(v_nargs_2279_, v_dummy_2278_);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_sub(v_nargs_2279_, v___x_2281_);
lean_dec(v_nargs_2279_);
lean_inc_ref(v_minor__type_2270_);
v___x_2283_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2266_, v_prods_2271_, v_motives_2267_, v_fs_2269_, v_minor__type_2270_, v_minor__type_2270_, v___x_2280_, v___x_2282_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
lean_dec_ref(v_fs_2269_);
return v___x_2283_;
}
else
{
lean_object* v_head_2284_; lean_object* v_tail_2285_; lean_object* v___x_2286_; 
v_head_2284_ = lean_ctor_get(v_a_2272_, 0);
lean_inc_n(v_head_2284_, 2);
v_tail_2285_ = lean_ctor_get(v_a_2272_, 1);
lean_inc(v_tail_2285_);
lean_dec_ref_known(v_a_2272_, 2);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
v___x_2286_ = lean_infer_type(v_head_2284_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___f_2288_; uint8_t v___x_2289_; lean_object* v___x_2290_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___f_2288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2288_, 0, v_motives_2267_);
lean_closure_set(v___f_2288_, 1, v_head_2284_);
lean_closure_set(v___f_2288_, 2, v_belows_2268_);
lean_closure_set(v___f_2288_, 3, v_prods_2271_);
lean_closure_set(v___f_2288_, 4, v_rlvl_2266_);
lean_closure_set(v___f_2288_, 5, v_fs_2269_);
lean_closure_set(v___f_2288_, 6, v_minor__type_2270_);
lean_closure_set(v___f_2288_, 7, v_tail_2285_);
v___x_2289_ = 0;
v___x_2290_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2287_, v___f_2288_, v___x_2289_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_);
return v___x_2290_;
}
else
{
lean_dec(v_tail_2285_);
lean_dec(v_head_2284_);
lean_dec_ref(v_prods_2271_);
lean_dec_ref(v_minor__type_2270_);
lean_dec_ref(v_fs_2269_);
lean_dec_ref(v_belows_2268_);
lean_dec_ref(v_motives_2267_);
lean_dec(v_rlvl_2266_);
return v___x_2286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2291_, lean_object* v_rlvl_2292_, lean_object* v_motives_2293_, lean_object* v_belows_2294_, lean_object* v_fs_2295_, lean_object* v_minor__type_2296_, lean_object* v_tail_2297_, uint8_t v___x_2298_, uint8_t v___x_2299_, uint8_t v___x_2300_, lean_object* v_arg_x27_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_inc_ref(v_arg_x27_2301_);
v___x_2307_ = lean_array_push(v_prods_2291_, v_arg_x27_2301_);
v___x_2308_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2292_, v_motives_2293_, v_belows_2294_, v_fs_2295_, v_minor__type_2296_, v___x_2307_, v_tail_2297_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_mk_empty_array_with_capacity(v___x_2310_);
v___x_2312_ = lean_array_push(v___x_2311_, v_arg_x27_2301_);
v___x_2313_ = l_Lean_Meta_mkLambdaFVars(v___x_2312_, v_a_2309_, v___x_2298_, v___x_2299_, v___x_2298_, v___x_2299_, v___x_2300_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec_ref(v___x_2312_);
return v___x_2313_;
}
else
{
lean_dec_ref(v_arg_x27_2301_);
return v___x_2308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2314_, lean_object* v_rlvl_2315_, lean_object* v_motives_2316_, lean_object* v_belows_2317_, lean_object* v_fs_2318_, lean_object* v_minor__type_2319_, lean_object* v_tail_2320_, lean_object* v___x_2321_, lean_object* v___x_2322_, lean_object* v___x_2323_, lean_object* v_arg_x27_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
uint8_t v___x_1743__boxed_2330_; uint8_t v___x_1744__boxed_2331_; uint8_t v___x_1745__boxed_2332_; lean_object* v_res_2333_; 
v___x_1743__boxed_2330_ = lean_unbox(v___x_2321_);
v___x_1744__boxed_2331_ = lean_unbox(v___x_2322_);
v___x_1745__boxed_2332_ = lean_unbox(v___x_2323_);
v_res_2333_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2314_, v_rlvl_2315_, v_motives_2316_, v_belows_2317_, v_fs_2318_, v_minor__type_2319_, v_tail_2320_, v___x_1743__boxed_2330_, v___x_1744__boxed_2331_, v___x_1745__boxed_2332_, v_arg_x27_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2334_, lean_object* v_head_2335_, lean_object* v_belows_2336_, lean_object* v_arg__type_2337_, lean_object* v_prods_2338_, lean_object* v_rlvl_2339_, lean_object* v_fs_2340_, lean_object* v_minor__type_2341_, lean_object* v_tail_2342_, lean_object* v_arg__args_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
if (lean_obj_tag(v_x_2344_) == 5)
{
lean_object* v_fn_2352_; lean_object* v_arg_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_fn_2352_ = lean_ctor_get(v_x_2344_, 0);
lean_inc_ref(v_fn_2352_);
v_arg_2353_ = lean_ctor_get(v_x_2344_, 1);
lean_inc_ref(v_arg_2353_);
lean_dec_ref_known(v_x_2344_, 2);
v___x_2354_ = lean_array_set(v_x_2345_, v_x_2346_, v_arg_2353_);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_sub(v_x_2346_, v___x_2355_);
lean_dec(v_x_2346_);
v_x_2344_ = v_fn_2352_;
v_x_2345_ = v___x_2354_;
v_x_2346_ = v___x_2356_;
goto _start;
}
else
{
lean_object* v___x_2358_; 
lean_dec(v_x_2346_);
v___x_2358_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2334_, v_x_2344_);
lean_dec_ref(v_x_2344_);
if (lean_obj_tag(v___x_2358_) == 1)
{
lean_object* v_val_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_val_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_val_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = l_Lean_Expr_fvarId_x21(v_head_2335_);
lean_dec_ref(v_head_2335_);
v___x_2361_ = l_Lean_FVarId_getUserName___redArg(v___x_2360_, v___y_2347_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_instInhabitedExpr;
v___x_2364_ = lean_array_get_borrowed(v___x_2363_, v_belows_2336_, v_val_2359_);
lean_dec(v_val_2359_);
lean_inc(v___x_2364_);
v___x_2365_ = l_Lean_mkAppN(v___x_2364_, v_x_2345_);
lean_dec_ref(v_x_2345_);
v___x_2366_ = l_Lean_Meta_mkPProd(v_arg__type_2337_, v___x_2365_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; uint8_t v___x_2368_; uint8_t v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = 0;
v___x_2369_ = 1;
v___x_2370_ = 1;
v___x_2371_ = l_Lean_Meta_mkForallFVars(v_arg__args_2343_, v_a_2367_, v___x_2368_, v___x_2369_, v___x_2369_, v___x_2370_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___f_2376_; lean_object* v___x_2377_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = lean_box(v___x_2368_);
v___x_2374_ = lean_box(v___x_2369_);
v___x_2375_ = lean_box(v___x_2370_);
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2376_, 0, v_prods_2338_);
lean_closure_set(v___f_2376_, 1, v_rlvl_2339_);
lean_closure_set(v___f_2376_, 2, v_motives_2334_);
lean_closure_set(v___f_2376_, 3, v_belows_2336_);
lean_closure_set(v___f_2376_, 4, v_fs_2340_);
lean_closure_set(v___f_2376_, 5, v_minor__type_2341_);
lean_closure_set(v___f_2376_, 6, v_tail_2342_);
lean_closure_set(v___f_2376_, 7, v___x_2373_);
lean_closure_set(v___f_2376_, 8, v___x_2374_);
lean_closure_set(v___f_2376_, 9, v___x_2375_);
v___x_2377_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2362_, v_a_2372_, v___f_2376_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
return v___x_2377_;
}
else
{
lean_dec(v_a_2362_);
lean_dec(v_tail_2342_);
lean_dec_ref(v_minor__type_2341_);
lean_dec_ref(v_fs_2340_);
lean_dec(v_rlvl_2339_);
lean_dec_ref(v_prods_2338_);
lean_dec_ref(v_belows_2336_);
lean_dec_ref(v_motives_2334_);
return v___x_2371_;
}
}
else
{
lean_dec(v_a_2362_);
lean_dec(v_tail_2342_);
lean_dec_ref(v_minor__type_2341_);
lean_dec_ref(v_fs_2340_);
lean_dec(v_rlvl_2339_);
lean_dec_ref(v_prods_2338_);
lean_dec_ref(v_belows_2336_);
lean_dec_ref(v_motives_2334_);
return v___x_2366_;
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_val_2359_);
lean_dec_ref(v_x_2345_);
lean_dec(v_tail_2342_);
lean_dec_ref(v_minor__type_2341_);
lean_dec_ref(v_fs_2340_);
lean_dec(v_rlvl_2339_);
lean_dec_ref(v_prods_2338_);
lean_dec_ref(v_arg__type_2337_);
lean_dec_ref(v_belows_2336_);
lean_dec_ref(v_motives_2334_);
v_a_2378_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2361_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2361_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2383_; 
if (v_isShared_2381_ == 0)
{
v___x_2383_ = v___x_2380_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_a_2378_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v___x_2386_; 
lean_dec(v___x_2358_);
lean_dec_ref(v_x_2345_);
lean_dec_ref(v_arg__type_2337_);
v___x_2386_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2339_, v_motives_2334_, v_belows_2336_, v_fs_2340_, v_minor__type_2341_, v_prods_2338_, v_tail_2342_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; uint8_t v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_mk_empty_array_with_capacity(v___x_2388_);
v___x_2390_ = lean_array_push(v___x_2389_, v_head_2335_);
v___x_2391_ = 0;
v___x_2392_ = 1;
v___x_2393_ = 1;
v___x_2394_ = l_Lean_Meta_mkLambdaFVars(v___x_2390_, v_a_2387_, v___x_2391_, v___x_2392_, v___x_2391_, v___x_2392_, v___x_2393_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec_ref(v___x_2390_);
return v___x_2394_;
}
else
{
lean_dec_ref(v_head_2335_);
return v___x_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2395_, lean_object* v_head_2396_, lean_object* v_belows_2397_, lean_object* v_prods_2398_, lean_object* v_rlvl_2399_, lean_object* v_fs_2400_, lean_object* v_minor__type_2401_, lean_object* v_tail_2402_, lean_object* v_arg__args_2403_, lean_object* v_arg__type_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_dummy_2410_; lean_object* v_nargs_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_dummy_2410_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2411_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2404_);
lean_inc(v_nargs_2411_);
v___x_2412_ = lean_mk_array(v_nargs_2411_, v_dummy_2410_);
v___x_2413_ = lean_unsigned_to_nat(1u);
v___x_2414_ = lean_nat_sub(v_nargs_2411_, v___x_2413_);
lean_dec(v_nargs_2411_);
lean_inc_ref(v_arg__type_2404_);
v___x_2415_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2395_, v_head_2396_, v_belows_2397_, v_arg__type_2404_, v_prods_2398_, v_rlvl_2399_, v_fs_2400_, v_minor__type_2401_, v_tail_2402_, v_arg__args_2403_, v_arg__type_2404_, v___x_2412_, v___x_2414_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2416_, lean_object* v_motives_2417_, lean_object* v_belows_2418_, lean_object* v_fs_2419_, lean_object* v_minor__type_2420_, lean_object* v_prods_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2416_, v_motives_2417_, v_belows_2418_, v_fs_2419_, v_minor__type_2420_, v_prods_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2429_ = _args[0];
lean_object* v_head_2430_ = _args[1];
lean_object* v_belows_2431_ = _args[2];
lean_object* v_arg__type_2432_ = _args[3];
lean_object* v_prods_2433_ = _args[4];
lean_object* v_rlvl_2434_ = _args[5];
lean_object* v_fs_2435_ = _args[6];
lean_object* v_minor__type_2436_ = _args[7];
lean_object* v_tail_2437_ = _args[8];
lean_object* v_arg__args_2438_ = _args[9];
lean_object* v_x_2439_ = _args[10];
lean_object* v_x_2440_ = _args[11];
lean_object* v_x_2441_ = _args[12];
lean_object* v___y_2442_ = _args[13];
lean_object* v___y_2443_ = _args[14];
lean_object* v___y_2444_ = _args[15];
lean_object* v___y_2445_ = _args[16];
lean_object* v___y_2446_ = _args[17];
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2429_, v_head_2430_, v_belows_2431_, v_arg__type_2432_, v_prods_2433_, v_rlvl_2434_, v_fs_2435_, v_minor__type_2436_, v_tail_2437_, v_arg__args_2438_, v_x_2439_, v_x_2440_, v_x_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v_arg__args_2438_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2448_, lean_object* v_motives_2449_, lean_object* v_belows_2450_, lean_object* v_fs_2451_, lean_object* v_minor__args_2452_, lean_object* v_minor__type_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2460_ = lean_array_to_list(v_minor__args_2452_);
v___x_2461_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2448_, v_motives_2449_, v_belows_2450_, v_fs_2451_, v_minor__type_2453_, v___x_2459_, v___x_2460_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2462_, lean_object* v_motives_2463_, lean_object* v_belows_2464_, lean_object* v_fs_2465_, lean_object* v_minor__args_2466_, lean_object* v_minor__type_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2462_, v_motives_2463_, v_belows_2464_, v_fs_2465_, v_minor__args_2466_, v_minor__type_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2474_, lean_object* v_motives_2475_, lean_object* v_belows_2476_, lean_object* v_fs_2477_, lean_object* v_minorType_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___f_2484_; uint8_t v___x_2485_; lean_object* v___x_2486_; 
v___f_2484_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2484_, 0, v_rlvl_2474_);
lean_closure_set(v___f_2484_, 1, v_motives_2475_);
lean_closure_set(v___f_2484_, 2, v_belows_2476_);
lean_closure_set(v___f_2484_, 3, v_fs_2477_);
v___x_2485_ = 0;
v___x_2486_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2478_, v___f_2484_, v___x_2485_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2487_, lean_object* v_motives_2488_, lean_object* v_belows_2489_, lean_object* v_fs_2490_, lean_object* v_minorType_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2487_, v_motives_2488_, v_belows_2489_, v_fs_2490_, v_minorType_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v___f_2504_; lean_object* v___x_27155__overap_2505_; lean_object* v___x_2506_; 
v___f_2504_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27155__overap_2505_ = lean_panic_fn_borrowed(v___f_2504_, v_msg_2498_);
lean_inc(v___y_2502_);
lean_inc_ref(v___y_2501_);
lean_inc(v___y_2500_);
lean_inc_ref(v___y_2499_);
v___x_2506_ = lean_apply_5(v___x_27155__overap_2505_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, lean_box(0));
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = l_Lean_Expr_hasMVar(v_e_2514_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_e_2514_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; lean_object* v_mctx_2520_; lean_object* v___x_2521_; lean_object* v_fst_2522_; lean_object* v_snd_2523_; lean_object* v___x_2524_; lean_object* v_cache_2525_; lean_object* v_zetaDeltaFVarIds_2526_; lean_object* v_postponed_2527_; lean_object* v_diag_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2537_; 
v___x_2519_ = lean_st_ref_get(v___y_2515_);
v_mctx_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_mctx_2520_);
lean_dec(v___x_2519_);
v___x_2521_ = l_Lean_instantiateMVarsCore(v_mctx_2520_, v_e_2514_);
v_fst_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_fst_2522_);
v_snd_2523_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2523_);
lean_dec_ref(v___x_2521_);
v___x_2524_ = lean_st_ref_take(v___y_2515_);
v_cache_2525_ = lean_ctor_get(v___x_2524_, 1);
v_zetaDeltaFVarIds_2526_ = lean_ctor_get(v___x_2524_, 2);
v_postponed_2527_ = lean_ctor_get(v___x_2524_, 3);
v_diag_2528_ = lean_ctor_get(v___x_2524_, 4);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2524_, 0);
lean_dec(v_unused_2538_);
v___x_2530_ = v___x_2524_;
v_isShared_2531_ = v_isSharedCheck_2537_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_diag_2528_);
lean_inc(v_postponed_2527_);
lean_inc(v_zetaDeltaFVarIds_2526_);
lean_inc(v_cache_2525_);
lean_dec(v___x_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2537_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v_snd_2523_);
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_snd_2523_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_cache_2525_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_zetaDeltaFVarIds_2526_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_postponed_2527_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_diag_2528_);
v___x_2533_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_st_ref_put(v___y_2515_, v___x_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_fst_2522_);
return v___x_2535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2539_, v___y_2540_);
lean_dec(v___y_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___x_2549_; 
v___x_2549_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2543_, v___y_2545_);
return v___x_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v_env_2561_; lean_object* v_toConstantVal_2562_; lean_object* v_value_2563_; lean_object* v_all_2564_; uint8_t v___y_2566_; lean_object* v_type_2574_; uint8_t v___x_2575_; 
v___x_2560_ = lean_st_ref_get(v___y_2558_);
v_env_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc_ref_n(v_env_2561_, 2);
lean_dec(v___x_2560_);
v_toConstantVal_2562_ = lean_ctor_get(v_thm_2557_, 0);
v_value_2563_ = lean_ctor_get(v_thm_2557_, 1);
v_all_2564_ = lean_ctor_get(v_thm_2557_, 2);
v_type_2574_ = lean_ctor_get(v_toConstantVal_2562_, 2);
v___x_2575_ = l_Lean_Environment_hasUnsafe(v_env_2561_, v_type_2574_);
if (v___x_2575_ == 0)
{
uint8_t v___x_2576_; 
v___x_2576_ = l_Lean_Environment_hasUnsafe(v_env_2561_, v_value_2563_);
v___y_2566_ = v___x_2576_;
goto v___jp_2565_;
}
else
{
lean_dec_ref(v_env_2561_);
v___y_2566_ = v___x_2575_;
goto v___jp_2565_;
}
v___jp_2565_:
{
if (v___y_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_thm_2557_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; uint8_t v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_inc(v_all_2564_);
lean_inc_ref(v_value_2563_);
lean_inc_ref(v_toConstantVal_2562_);
lean_dec_ref(v_thm_2557_);
v___x_2569_ = lean_box(0);
v___x_2570_ = 0;
v___x_2571_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2571_, 0, v_toConstantVal_2562_);
lean_ctor_set(v___x_2571_, 1, v_value_2563_);
lean_ctor_set(v___x_2571_, 2, v___x_2569_);
lean_ctor_set(v___x_2571_, 3, v_all_2564_);
lean_ctor_set_uint8(v___x_2571_, sizeof(void*)*4, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
v___x_2573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v_res_2580_; 
v_res_2580_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2577_, v___y_2578_);
lean_dec(v___y_2578_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2581_, v___y_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2596_, lean_object* v___x_2597_, lean_object* v___x_2598_, lean_object* v_all_2599_, lean_object* v___x_2600_, lean_object* v___x_2601_, lean_object* v___x_2602_, lean_object* v_x_2603_){
_start:
{
lean_object* v___y_2605_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
v___x_2609_ = lean_array_get_size(v_all_2599_);
v___x_2610_ = lean_nat_dec_lt(v_x_2603_, v___x_2609_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2611_ = lean_array_get_borrowed(v___x_2600_, v_all_2599_, v___x_2601_);
v___x_2612_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2613_ = lean_nat_sub(v_x_2603_, v___x_2609_);
v___x_2614_ = lean_nat_add(v___x_2613_, v___x_2602_);
lean_dec(v___x_2613_);
v___x_2615_ = l_Nat_reprFast(v___x_2614_);
v___x_2616_ = lean_string_append(v___x_2612_, v___x_2615_);
lean_dec_ref(v___x_2615_);
lean_inc(v___x_2611_);
v___x_2617_ = l_Lean_Name_str___override(v___x_2611_, v___x_2616_);
v___y_2605_ = v___x_2617_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_array_fget_borrowed(v_all_2599_, v_x_2603_);
lean_inc(v___x_2618_);
v___x_2619_ = l_Lean_mkBelowName(v___x_2618_);
v___y_2605_ = v___x_2619_;
goto v___jp_2604_;
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = l_Lean_Expr_const___override(v___y_2605_, v___x_2596_);
v___x_2607_ = l_Array_append___redArg(v___x_2597_, v___x_2598_);
v___x_2608_ = l_Lean_mkAppN(v___x_2606_, v___x_2607_);
lean_dec_ref(v___x_2607_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2620_, lean_object* v___x_2621_, lean_object* v___x_2622_, lean_object* v_all_2623_, lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v_x_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2620_, v___x_2621_, v___x_2622_, v_all_2623_, v___x_2624_, v___x_2625_, v___x_2626_, v_x_2627_);
lean_dec(v_x_2627_);
lean_dec(v___x_2626_);
lean_dec(v___x_2625_);
lean_dec(v___x_2624_);
lean_dec_ref(v_all_2623_);
lean_dec_ref(v___x_2622_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2629_, lean_object* v___x_2630_, uint8_t v___x_2631_, lean_object* v_targs_2632_, lean_object* v_x_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = l_Lean_mkAppN(v_a_2629_, v_targs_2632_);
v___x_2640_ = l_Lean_mkAppN(v___x_2630_, v_targs_2632_);
v___x_2641_ = l_Lean_Meta_mkPProd(v___x_2639_, v___x_2640_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; uint8_t v___x_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = 0;
v___x_2644_ = 1;
v___x_2645_ = l_Lean_Meta_mkLambdaFVars(v_targs_2632_, v_a_2642_, v___x_2643_, v___x_2631_, v___x_2643_, v___x_2631_, v___x_2644_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2645_;
}
else
{
return v___x_2641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2646_, lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v_targs_2649_, lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_30350__boxed_2656_; lean_object* v_res_2657_; 
v___x_30350__boxed_2656_ = lean_unbox(v___x_2648_);
v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2646_, v___x_2647_, v___x_30350__boxed_2656_, v_targs_2649_, v_x_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec_ref(v_x_2650_);
lean_dec_ref(v_targs_2649_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2658_, lean_object* v___x_2659_, lean_object* v_as_2660_, size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_b_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
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
lean_object* v_snd_2671_; lean_object* v_fst_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2729_; 
v_snd_2671_ = lean_ctor_get(v_b_2663_, 1);
v_fst_2672_ = lean_ctor_get(v_b_2663_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_b_2663_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2674_ = v_b_2663_;
v_isShared_2675_ = v_isSharedCheck_2729_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_snd_2671_);
lean_inc(v_fst_2672_);
lean_dec(v_b_2663_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2729_;
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
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2725_; 
lean_inc(v_stop_2678_);
lean_inc(v_start_2677_);
lean_inc_ref(v_array_2676_);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_snd_2671_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; lean_object* v_unused_2727_; lean_object* v_unused_2728_; 
v_unused_2726_ = lean_ctor_get(v_snd_2671_, 2);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_snd_2671_, 1);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_snd_2671_, 0);
lean_dec(v_unused_2728_);
v___x_2685_ = v_snd_2671_;
v_isShared_2686_ = v_isSharedCheck_2725_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_snd_2671_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2725_;
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
lean_object* v_a_2689_; uint8_t v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___f_2693_; uint8_t v___x_2694_; lean_object* v___x_2695_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
v___x_2690_ = lean_nat_dec_lt(v___x_2658_, v___x_2659_);
v___x_2691_ = lean_array_fget_borrowed(v_array_2676_, v_start_2677_);
v___x_2692_ = lean_box(v___x_2690_);
lean_inc(v___x_2691_);
lean_inc(v_a_2687_);
v___f_2693_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2693_, 0, v_a_2687_);
lean_closure_set(v___f_2693_, 1, v___x_2691_);
lean_closure_set(v___f_2693_, 2, v___x_2692_);
v___x_2694_ = 0;
v___x_2695_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2689_, v___f_2693_, v___x_2694_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_start_2677_, v___x_2697_);
lean_dec(v_start_2677_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2698_);
v___x_2700_ = v___x_2685_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_array_2676_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2698_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v_stop_2678_);
v___x_2700_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = l_Lean_Expr_app___override(v_fst_2672_, v_a_2696_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 1, v___x_2700_);
lean_ctor_set(v___x_2674_, 0, v___x_2701_);
v___x_2703_ = v___x_2674_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2700_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
size_t v___x_2704_; size_t v___x_2705_; 
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2662_, v___x_2704_);
v_i_2662_ = v___x_2705_;
v_b_2663_ = v___x_2703_;
goto _start;
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2685_);
lean_dec(v_stop_2678_);
lean_dec(v_start_2677_);
lean_dec_ref(v_array_2676_);
lean_del_object(v___x_2674_);
lean_dec(v_fst_2672_);
v_a_2709_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2695_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2695_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2685_);
lean_dec(v_stop_2678_);
lean_dec(v_start_2677_);
lean_dec_ref(v_array_2676_);
lean_del_object(v___x_2674_);
lean_dec(v_fst_2672_);
v_a_2717_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2688_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2688_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2730_, lean_object* v___x_2731_, lean_object* v_as_2732_, lean_object* v_sz_2733_, lean_object* v_i_2734_, lean_object* v_b_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2733_);
lean_dec(v_sz_2733_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2734_);
lean_dec(v_i_2734_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2730_, v___x_2731_, v_as_2732_, v_sz_boxed_2741_, v_i_boxed_2742_, v_b_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v_as_2732_);
lean_dec(v___x_2731_);
lean_dec(v___x_2730_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2744_, size_t v_sz_2745_, size_t v_i_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
uint8_t v___x_2753_; 
v___x_2753_ = lean_usize_dec_lt(v_i_2746_, v_sz_2745_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_b_2747_);
return v___x_2754_;
}
else
{
lean_object* v_a_2755_; lean_object* v_toInductionSubgoal_2756_; lean_object* v_mvarId_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v_a_2755_ = lean_array_uget_borrowed(v_as_2744_, v_i_2746_);
v_toInductionSubgoal_2756_ = lean_ctor_get(v_a_2755_, 0);
v_mvarId_2757_ = lean_ctor_get(v_toInductionSubgoal_2756_, 0);
v___x_2758_ = 0;
lean_inc(v_mvarId_2757_);
v___x_2759_ = l_Lean_MVarId_refl(v_mvarId_2757_, v___x_2758_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; size_t v___x_2761_; size_t v___x_2762_; 
lean_dec_ref_known(v___x_2759_, 1);
v___x_2760_ = lean_box(0);
v___x_2761_ = ((size_t)1ULL);
v___x_2762_ = lean_usize_add(v_i_2746_, v___x_2761_);
v_i_2746_ = v___x_2762_;
v_b_2747_ = v___x_2760_;
goto _start;
}
else
{
return v___x_2759_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2764_, lean_object* v_sz_2765_, lean_object* v_i_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
size_t v_sz_boxed_2773_; size_t v_i_boxed_2774_; lean_object* v_res_2775_; 
v_sz_boxed_2773_ = lean_unbox_usize(v_sz_2765_);
lean_dec(v_sz_2765_);
v_i_boxed_2774_ = lean_unbox_usize(v_i_2766_);
lean_dec(v_i_2766_);
v_res_2775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2764_, v_sz_boxed_2773_, v_i_boxed_2774_, v_b_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec_ref(v_as_2764_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_fs_2779_, lean_object* v_as_2780_, size_t v_sz_2781_, size_t v_i_2782_, lean_object* v_b_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_usize_dec_lt(v_i_2782_, v_sz_2781_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_dec_ref(v_fs_2779_);
lean_dec_ref(v___x_2778_);
lean_dec_ref(v___x_2777_);
lean_dec(v___x_2776_);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v_b_2783_);
return v___x_2790_;
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2792_; 
v_a_2791_ = lean_array_uget_borrowed(v_as_2780_, v_i_2782_);
lean_inc(v___y_2787_);
lean_inc_ref(v___y_2786_);
lean_inc(v___y_2785_);
lean_inc_ref(v___y_2784_);
lean_inc(v_a_2791_);
v___x_2792_ = lean_infer_type(v_a_2791_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
lean_inc_ref(v_fs_2779_);
lean_inc_ref(v___x_2778_);
lean_inc_ref(v___x_2777_);
lean_inc(v___x_2776_);
v___x_2794_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2776_, v___x_2777_, v___x_2778_, v_fs_2779_, v_a_2793_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; size_t v___x_2797_; size_t v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = l_Lean_Expr_app___override(v_b_2783_, v_a_2795_);
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2782_, v___x_2797_);
v_i_2782_ = v___x_2798_;
v_b_2783_ = v___x_2796_;
goto _start;
}
else
{
lean_dec_ref(v_b_2783_);
lean_dec_ref(v_fs_2779_);
lean_dec_ref(v___x_2778_);
lean_dec_ref(v___x_2777_);
lean_dec(v___x_2776_);
return v___x_2794_;
}
}
else
{
lean_dec_ref(v_b_2783_);
lean_dec_ref(v_fs_2779_);
lean_dec_ref(v___x_2778_);
lean_dec_ref(v___x_2777_);
lean_dec(v___x_2776_);
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v___x_2802_, lean_object* v_fs_2803_, lean_object* v_as_2804_, lean_object* v_sz_2805_, lean_object* v_i_2806_, lean_object* v_b_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
size_t v_sz_boxed_2813_; size_t v_i_boxed_2814_; lean_object* v_res_2815_; 
v_sz_boxed_2813_ = lean_unbox_usize(v_sz_2805_);
lean_dec(v_sz_2805_);
v_i_boxed_2814_ = lean_unbox_usize(v_i_2806_);
lean_dec(v_i_2806_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2800_, v___x_2801_, v___x_2802_, v_fs_2803_, v_as_2804_, v_sz_boxed_2813_, v_i_boxed_2814_, v_b_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec_ref(v_as_2804_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2816_, lean_object* v_tail_2817_, lean_object* v_recName_2818_, lean_object* v___x_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v___x_2822_, lean_object* v___x_2823_, size_t v_sz_2824_, size_t v___x_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v_val_2832_, uint8_t v___x_2833_, lean_object* v_brecOnGoName_2834_, lean_object* v_levelParams_2835_, lean_object* v___x_2836_, lean_object* v_brecOnName_2837_, lean_object* v___x_2838_, lean_object* v_brecOnEqName_2839_, lean_object* v_fs_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_inc(v___x_2816_);
v___x_2846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2816_);
lean_ctor_set(v___x_2846_, 1, v_tail_2817_);
v___x_2847_ = l_Lean_Expr_const___override(v_recName_2818_, v___x_2846_);
v___x_2848_ = l_Lean_mkAppN(v___x_2847_, v___x_2819_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___x_2820_);
v___x_2850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2821_, v___x_2822_, v___x_2823_, v_sz_2824_, v___x_2825_, v___x_2849_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v_fst_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_3213_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v_fst_2852_ = lean_ctor_get(v_a_2851_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_a_2851_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v_a_2851_, 1);
lean_dec(v_unused_3214_);
v___x_2854_ = v_a_2851_;
v_isShared_2855_ = v_isSharedCheck_3213_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_fst_2852_);
lean_dec(v_a_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_3213_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
size_t v_sz_2856_; lean_object* v___x_2857_; 
v_sz_2856_ = lean_array_size(v___x_2826_);
lean_inc_ref(v_fs_2840_);
lean_inc_ref(v___x_2827_);
lean_inc_ref(v___x_2823_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2816_, v___x_2823_, v___x_2827_, v_fs_2840_, v___x_2826_, v_sz_2856_, v___x_2825_, v_fst_2852_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l_Lean_mkAppN(v_a_2858_, v___x_2828_);
lean_inc_ref_n(v___x_2829_, 3);
v___x_2860_ = l_Lean_Expr_app___override(v___x_2859_, v___x_2829_);
v___x_2861_ = l_Array_append___redArg(v___x_2819_, v___x_2823_);
v___x_2862_ = l_Array_append___redArg(v___x_2861_, v___x_2828_);
v___x_2863_ = lean_mk_empty_array_with_capacity(v___x_2830_);
v___x_2864_ = lean_array_push(v___x_2863_, v___x_2829_);
v___x_2865_ = lean_array_get(v___x_2831_, v___x_2823_, v_val_2832_);
lean_dec_ref(v___x_2823_);
v___x_2866_ = lean_array_push(v___x_2828_, v___x_2829_);
v___x_2867_ = l_Lean_mkAppN(v___x_2865_, v___x_2866_);
v___x_2868_ = lean_array_get(v___x_2831_, v___x_2827_, v_val_2832_);
lean_dec_ref(v___x_2827_);
v___x_2869_ = l_Lean_mkAppN(v___x_2868_, v___x_2866_);
lean_inc_ref(v___x_2867_);
v___x_2870_ = l_Lean_Meta_mkPProd(v___x_2867_, v___x_2869_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___x_2872_ = l_Array_append___redArg(v___x_2862_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2873_ = l_Array_append___redArg(v___x_2872_, v_fs_2840_);
v___x_2874_ = 0;
v___x_2875_ = 1;
v___x_2876_ = l_Lean_Meta_mkForallFVars(v___x_2873_, v_a_2871_, v___x_2874_, v___x_2833_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = l_Lean_Meta_mkLambdaFVars(v___x_2873_, v___x_2860_, v___x_2874_, v___x_2833_, v___x_2874_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_3180_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___x_2880_ = lean_box(1);
lean_inc(v_levelParams_2835_);
lean_inc(v_brecOnGoName_2834_);
v___x_2881_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2834_, v_levelParams_2835_, v_a_2877_, v_a_2879_, v___x_2880_, v___y_2844_);
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_3180_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_3180_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
lean_inc(v_a_2882_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set_tag(v___x_2884_, 1);
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_3179_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_addDecl(v___x_2887_, v___x_2874_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_toConstantVal_2889_; lean_object* v_name_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3176_; 
lean_dec_ref_known(v___x_2888_, 1);
v_toConstantVal_2889_ = lean_ctor_get(v_a_2882_, 0);
lean_inc_ref(v_toConstantVal_2889_);
lean_dec(v_a_2882_);
v_name_2890_ = lean_ctor_get(v_toConstantVal_2889_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_toConstantVal_2889_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; 
v_unused_3177_ = lean_ctor_get(v_toConstantVal_2889_, 2);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_toConstantVal_2889_, 1);
lean_dec(v_unused_3178_);
v___x_2892_ = v_toConstantVal_2889_;
v_isShared_2893_ = v_isSharedCheck_3176_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_name_2890_);
lean_dec(v_toConstantVal_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3176_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_env_2896_; lean_object* v_nextMacroScope_2897_; lean_object* v_ngen_2898_; lean_object* v_auxDeclNGen_2899_; lean_object* v_traceState_2900_; lean_object* v_messages_2901_; lean_object* v_infoState_2902_; lean_object* v_snapshotTasks_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_3174_; 
lean_inc(v_name_2890_);
v___x_2894_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2890_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___x_2894_);
v___x_2895_ = lean_st_ref_take(v___y_2844_);
v_env_2896_ = lean_ctor_get(v___x_2895_, 0);
v_nextMacroScope_2897_ = lean_ctor_get(v___x_2895_, 1);
v_ngen_2898_ = lean_ctor_get(v___x_2895_, 2);
v_auxDeclNGen_2899_ = lean_ctor_get(v___x_2895_, 3);
v_traceState_2900_ = lean_ctor_get(v___x_2895_, 4);
v_messages_2901_ = lean_ctor_get(v___x_2895_, 6);
v_infoState_2902_ = lean_ctor_get(v___x_2895_, 7);
v_snapshotTasks_2903_ = lean_ctor_get(v___x_2895_, 8);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_2895_, 5);
lean_dec(v_unused_3175_);
v___x_2905_ = v___x_2895_;
v_isShared_2906_ = v_isSharedCheck_3174_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snapshotTasks_2903_);
lean_inc(v_infoState_2902_);
lean_inc(v_messages_2901_);
lean_inc(v_traceState_2900_);
lean_inc(v_auxDeclNGen_2899_);
lean_inc(v_ngen_2898_);
lean_inc(v_nextMacroScope_2897_);
lean_inc(v_env_2896_);
lean_dec(v___x_2895_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_3174_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = l_Lean_addProtected(v_env_2896_, v_name_2890_);
v___x_2908_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 5, v___x_2908_);
lean_ctor_set(v___x_2905_, 0, v___x_2907_);
v___x_2910_ = v___x_2905_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_nextMacroScope_2897_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_ngen_2898_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_auxDeclNGen_2899_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_traceState_2900_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_3173_, 6, v_messages_2901_);
lean_ctor_set(v_reuseFailAlloc_3173_, 7, v_infoState_2902_);
lean_ctor_set(v_reuseFailAlloc_3173_, 8, v_snapshotTasks_2903_);
v___x_2910_ = v_reuseFailAlloc_3173_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_mctx_2913_; lean_object* v_zetaDeltaFVarIds_2914_; lean_object* v_postponed_2915_; lean_object* v_diag_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_3171_; 
v___x_2911_ = lean_st_ref_put(v___y_2844_, v___x_2910_);
v___x_2912_ = lean_st_ref_take(v___y_2842_);
v_mctx_2913_ = lean_ctor_get(v___x_2912_, 0);
v_zetaDeltaFVarIds_2914_ = lean_ctor_get(v___x_2912_, 2);
v_postponed_2915_ = lean_ctor_get(v___x_2912_, 3);
v_diag_2916_ = lean_ctor_get(v___x_2912_, 4);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; 
v_unused_3172_ = lean_ctor_get(v___x_2912_, 1);
lean_dec(v_unused_3172_);
v___x_2918_ = v___x_2912_;
v_isShared_2919_ = v_isSharedCheck_3171_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_diag_2916_);
lean_inc(v_postponed_2915_);
lean_inc(v_zetaDeltaFVarIds_2914_);
lean_inc(v_mctx_2913_);
lean_dec(v___x_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_3171_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2920_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 1, v___x_2920_);
v___x_2922_ = v___x_2918_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_mctx_2913_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_zetaDeltaFVarIds_2914_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_postponed_2915_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_diag_2916_);
v___x_2922_ = v_reuseFailAlloc_3170_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2923_ = lean_st_ref_put(v___y_2842_, v___x_2922_);
lean_inc(v___x_2836_);
v___x_2924_ = l_Lean_Expr_const___override(v_brecOnGoName_2834_, v___x_2836_);
v___x_2925_ = l_Lean_mkAppN(v___x_2924_, v___x_2873_);
lean_inc_ref(v___x_2925_);
v___x_2926_ = l_Lean_Meta_mkPProdFstM(v___x_2925_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = l_Lean_Meta_mkLambdaFVars(v___x_2873_, v_a_2927_, v___x_2874_, v___x_2833_, v___x_2874_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
v___x_2930_ = l_Lean_Meta_mkForallFVars(v___x_2873_, v___x_2867_, v___x_2874_, v___x_2833_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3145_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2930_, 1);
lean_inc(v_levelParams_2835_);
v___x_2932_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2837_, v_levelParams_2835_, v_a_2931_, v_a_2929_, v___x_2880_, v___y_2844_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_3145_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3145_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
lean_inc(v_a_2933_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set_tag(v___x_2935_, 1);
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_3144_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_addDecl(v___x_2938_, v___x_2874_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_toConstantVal_2940_; lean_object* v_name_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref_known(v___x_2939_, 1);
v_toConstantVal_2940_ = lean_ctor_get(v_a_2933_, 0);
lean_inc_ref(v_toConstantVal_2940_);
lean_dec(v_a_2933_);
v_name_2941_ = lean_ctor_get(v_toConstantVal_2940_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_toConstantVal_2940_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; lean_object* v_unused_3143_; 
v_unused_3142_ = lean_ctor_get(v_toConstantVal_2940_, 2);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_toConstantVal_2940_, 1);
lean_dec(v_unused_3143_);
v___x_2943_ = v_toConstantVal_2940_;
v_isShared_2944_ = v_isSharedCheck_3141_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_name_2941_);
lean_dec(v_toConstantVal_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_3141_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v_env_2947_; lean_object* v_nextMacroScope_2948_; lean_object* v_ngen_2949_; lean_object* v_auxDeclNGen_2950_; lean_object* v_traceState_2951_; lean_object* v_messages_2952_; lean_object* v_infoState_2953_; lean_object* v_snapshotTasks_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3139_; 
lean_inc(v_name_2941_);
v___x_2945_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2941_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___x_2945_);
v___x_2946_ = lean_st_ref_take(v___y_2844_);
v_env_2947_ = lean_ctor_get(v___x_2946_, 0);
v_nextMacroScope_2948_ = lean_ctor_get(v___x_2946_, 1);
v_ngen_2949_ = lean_ctor_get(v___x_2946_, 2);
v_auxDeclNGen_2950_ = lean_ctor_get(v___x_2946_, 3);
v_traceState_2951_ = lean_ctor_get(v___x_2946_, 4);
v_messages_2952_ = lean_ctor_get(v___x_2946_, 6);
v_infoState_2953_ = lean_ctor_get(v___x_2946_, 7);
v_snapshotTasks_2954_ = lean_ctor_get(v___x_2946_, 8);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_2946_, 5);
lean_dec(v_unused_3140_);
v___x_2956_ = v___x_2946_;
v_isShared_2957_ = v_isSharedCheck_3139_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_snapshotTasks_2954_);
lean_inc(v_infoState_2953_);
lean_inc(v_messages_2952_);
lean_inc(v_traceState_2951_);
lean_inc(v_auxDeclNGen_2950_);
lean_inc(v_ngen_2949_);
lean_inc(v_nextMacroScope_2948_);
lean_inc(v_env_2947_);
lean_dec(v___x_2946_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3139_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2960_; 
lean_inc(v_name_2941_);
v___x_2958_ = l_Lean_markAuxRecursor(v_env_2947_, v_name_2941_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 5, v___x_2908_);
lean_ctor_set(v___x_2956_, 0, v___x_2958_);
v___x_2960_ = v___x_2956_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_nextMacroScope_2948_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_ngen_2949_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_auxDeclNGen_2950_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_traceState_2951_);
lean_ctor_set(v_reuseFailAlloc_3138_, 5, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_3138_, 6, v_messages_2952_);
lean_ctor_set(v_reuseFailAlloc_3138_, 7, v_infoState_2953_);
lean_ctor_set(v_reuseFailAlloc_3138_, 8, v_snapshotTasks_2954_);
v___x_2960_ = v_reuseFailAlloc_3138_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v_mctx_2963_; lean_object* v_zetaDeltaFVarIds_2964_; lean_object* v_postponed_2965_; lean_object* v_diag_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3136_; 
v___x_2961_ = lean_st_ref_put(v___y_2844_, v___x_2960_);
v___x_2962_ = lean_st_ref_take(v___y_2842_);
v_mctx_2963_ = lean_ctor_get(v___x_2962_, 0);
v_zetaDeltaFVarIds_2964_ = lean_ctor_get(v___x_2962_, 2);
v_postponed_2965_ = lean_ctor_get(v___x_2962_, 3);
v_diag_2966_ = lean_ctor_get(v___x_2962_, 4);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_2962_, 1);
lean_dec(v_unused_3137_);
v___x_2968_ = v___x_2962_;
v_isShared_2969_ = v_isSharedCheck_3136_;
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
v_isShared_2969_ = v_isSharedCheck_3136_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 1, v___x_2920_);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_mctx_2963_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_zetaDeltaFVarIds_2964_);
lean_ctor_set(v_reuseFailAlloc_3135_, 3, v_postponed_2965_);
lean_ctor_set(v_reuseFailAlloc_3135_, 4, v_diag_2966_);
v___x_2971_ = v_reuseFailAlloc_3135_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v_env_2974_; lean_object* v_nextMacroScope_2975_; lean_object* v_ngen_2976_; lean_object* v_auxDeclNGen_2977_; lean_object* v_traceState_2978_; lean_object* v_messages_2979_; lean_object* v_infoState_2980_; lean_object* v_snapshotTasks_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3133_; 
v___x_2972_ = lean_st_ref_put(v___y_2842_, v___x_2971_);
v___x_2973_ = lean_st_ref_take(v___y_2844_);
v_env_2974_ = lean_ctor_get(v___x_2973_, 0);
v_nextMacroScope_2975_ = lean_ctor_get(v___x_2973_, 1);
v_ngen_2976_ = lean_ctor_get(v___x_2973_, 2);
v_auxDeclNGen_2977_ = lean_ctor_get(v___x_2973_, 3);
v_traceState_2978_ = lean_ctor_get(v___x_2973_, 4);
v_messages_2979_ = lean_ctor_get(v___x_2973_, 6);
v_infoState_2980_ = lean_ctor_get(v___x_2973_, 7);
v_snapshotTasks_2981_ = lean_ctor_get(v___x_2973_, 8);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v___x_2973_, 5);
lean_dec(v_unused_3134_);
v___x_2983_ = v___x_2973_;
v_isShared_2984_ = v_isSharedCheck_3133_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_snapshotTasks_2981_);
lean_inc(v_infoState_2980_);
lean_inc(v_messages_2979_);
lean_inc(v_traceState_2978_);
lean_inc(v_auxDeclNGen_2977_);
lean_inc(v_ngen_2976_);
lean_inc(v_nextMacroScope_2975_);
lean_inc(v_env_2974_);
lean_dec(v___x_2973_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3133_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; 
lean_inc(v_name_2941_);
v___x_2985_ = l_Lean_addProtected(v_env_2974_, v_name_2941_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 5, v___x_2908_);
lean_ctor_set(v___x_2983_, 0, v___x_2985_);
v___x_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_2985_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_nextMacroScope_2975_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_ngen_2976_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_auxDeclNGen_2977_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_traceState_2978_);
lean_ctor_set(v_reuseFailAlloc_3132_, 5, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_3132_, 6, v_messages_2979_);
lean_ctor_set(v_reuseFailAlloc_3132_, 7, v_infoState_2980_);
lean_ctor_set(v_reuseFailAlloc_3132_, 8, v_snapshotTasks_2981_);
v___x_2987_ = v_reuseFailAlloc_3132_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_mctx_2990_; lean_object* v_zetaDeltaFVarIds_2991_; lean_object* v_postponed_2992_; lean_object* v_diag_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3130_; 
v___x_2988_ = lean_st_ref_put(v___y_2844_, v___x_2987_);
v___x_2989_ = lean_st_ref_take(v___y_2842_);
v_mctx_2990_ = lean_ctor_get(v___x_2989_, 0);
v_zetaDeltaFVarIds_2991_ = lean_ctor_get(v___x_2989_, 2);
v_postponed_2992_ = lean_ctor_get(v___x_2989_, 3);
v_diag_2993_ = lean_ctor_get(v___x_2989_, 4);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v___x_2989_, 1);
lean_dec(v_unused_3131_);
v___x_2995_ = v___x_2989_;
v_isShared_2996_ = v_isSharedCheck_3130_;
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
v_isShared_2996_ = v_isSharedCheck_3130_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_2920_);
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_mctx_2990_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_zetaDeltaFVarIds_2991_);
lean_ctor_set(v_reuseFailAlloc_3129_, 3, v_postponed_2992_);
lean_ctor_set(v_reuseFailAlloc_3129_, 4, v_diag_2993_);
v___x_2998_ = v_reuseFailAlloc_3129_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_st_ref_put(v___y_2842_, v___x_2998_);
v___x_3000_ = l_Lean_Meta_mkPProdSndM(v___x_2925_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = l_Lean_Expr_const___override(v_name_2941_, v___x_2836_);
v___x_3003_ = l_Lean_mkAppN(v___x_3002_, v___x_2873_);
v___x_3004_ = lean_array_get(v___x_2831_, v_fs_2840_, v_val_2832_);
lean_dec_ref(v_fs_2840_);
v___x_3005_ = l_Lean_mkAppN(v___x_3004_, v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_3006_ = l_Lean_Expr_app___override(v___x_3005_, v_a_3001_);
v___x_3007_ = l_Lean_Meta_mkEq(v___x_3003_, v___x_3006_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc_n(v_a_3008_, 2);
lean_dec_ref_known(v___x_3007_, 1);
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3008_, v___x_3009_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = l_Lean_Expr_mvarId_x21(v_a_3011_);
v___x_3013_ = l_Lean_Expr_fvarId_x21(v___x_2829_);
lean_dec_ref(v___x_2829_);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_2838_);
v___x_3015_ = lean_box(0);
v___x_3016_ = l_Lean_MVarId_cases(v___x_3012_, v___x_3013_, v___x_3014_, v___x_2874_, v___x_3015_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; size_t v_sz_3019_; lean_object* v___x_3020_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = lean_box(0);
v_sz_3019_ = lean_array_size(v_a_3017_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3017_, v_sz_3019_, v___x_2825_, v___x_3018_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec(v_a_3017_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3020_, 1);
v___x_3021_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3011_, v___y_2842_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_Meta_mkForallFVars(v___x_2873_, v_a_3008_, v___x_2874_, v___x_2833_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = l_Lean_Meta_mkLambdaFVars(v___x_2873_, v_a_3022_, v___x_2874_, v___x_2833_, v___x_2874_, v___x_2833_, v___x_2875_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___x_2873_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3028_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
lean_inc(v_brecOnEqName_2839_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 2, v_a_3024_);
lean_ctor_set(v___x_2943_, 1, v_levelParams_2835_);
lean_ctor_set(v___x_2943_, 0, v_brecOnEqName_2839_);
v___x_3028_ = v___x_2943_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_brecOnEqName_2839_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_levelParams_2835_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_a_3024_);
v___x_3028_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3029_ = lean_box(0);
lean_inc(v_brecOnEqName_2839_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set_tag(v___x_2854_, 1);
lean_ctor_set(v___x_2854_, 1, v___x_3029_);
lean_ctor_set(v___x_2854_, 0, v_brecOnEqName_2839_);
v___x_3031_ = v___x_2854_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_brecOnEqName_2839_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 2, v___x_3031_);
lean_ctor_set(v___x_2892_, 1, v_a_3026_);
lean_ctor_set(v___x_2892_, 0, v___x_3028_);
v___x_3033_ = v___x_2892_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v_a_3026_);
lean_ctor_set(v_reuseFailAlloc_3078_, 2, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v_a_3035_; lean_object* v___x_3036_; 
v___x_3034_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3033_, v___y_2844_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = l_Lean_addDecl(v_a_3035_, v___x_2874_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3076_; 
v_isSharedCheck_3076_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v___x_3036_, 0);
lean_dec(v_unused_3077_);
v___x_3038_ = v___x_3036_;
v_isShared_3039_ = v_isSharedCheck_3076_;
goto v_resetjp_3037_;
}
else
{
lean_dec(v___x_3036_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3076_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v_env_3041_; lean_object* v_nextMacroScope_3042_; lean_object* v_ngen_3043_; lean_object* v_auxDeclNGen_3044_; lean_object* v_traceState_3045_; lean_object* v_messages_3046_; lean_object* v_infoState_3047_; lean_object* v_snapshotTasks_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3074_; 
v___x_3040_ = lean_st_ref_take(v___y_2844_);
v_env_3041_ = lean_ctor_get(v___x_3040_, 0);
v_nextMacroScope_3042_ = lean_ctor_get(v___x_3040_, 1);
v_ngen_3043_ = lean_ctor_get(v___x_3040_, 2);
v_auxDeclNGen_3044_ = lean_ctor_get(v___x_3040_, 3);
v_traceState_3045_ = lean_ctor_get(v___x_3040_, 4);
v_messages_3046_ = lean_ctor_get(v___x_3040_, 6);
v_infoState_3047_ = lean_ctor_get(v___x_3040_, 7);
v_snapshotTasks_3048_ = lean_ctor_get(v___x_3040_, 8);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_3040_, 5);
lean_dec(v_unused_3075_);
v___x_3050_ = v___x_3040_;
v_isShared_3051_ = v_isSharedCheck_3074_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_snapshotTasks_3048_);
lean_inc(v_infoState_3047_);
lean_inc(v_messages_3046_);
lean_inc(v_traceState_3045_);
lean_inc(v_auxDeclNGen_3044_);
lean_inc(v_ngen_3043_);
lean_inc(v_nextMacroScope_3042_);
lean_inc(v_env_3041_);
lean_dec(v___x_3040_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3074_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = l_Lean_addProtected(v_env_3041_, v_brecOnEqName_2839_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 5, v___x_2908_);
lean_ctor_set(v___x_3050_, 0, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_nextMacroScope_3042_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_ngen_3043_);
lean_ctor_set(v_reuseFailAlloc_3073_, 3, v_auxDeclNGen_3044_);
lean_ctor_set(v_reuseFailAlloc_3073_, 4, v_traceState_3045_);
lean_ctor_set(v_reuseFailAlloc_3073_, 5, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_3073_, 6, v_messages_3046_);
lean_ctor_set(v_reuseFailAlloc_3073_, 7, v_infoState_3047_);
lean_ctor_set(v_reuseFailAlloc_3073_, 8, v_snapshotTasks_3048_);
v___x_3054_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v_mctx_3057_; lean_object* v_zetaDeltaFVarIds_3058_; lean_object* v_postponed_3059_; lean_object* v_diag_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3071_; 
v___x_3055_ = lean_st_ref_put(v___y_2844_, v___x_3054_);
v___x_3056_ = lean_st_ref_take(v___y_2842_);
v_mctx_3057_ = lean_ctor_get(v___x_3056_, 0);
v_zetaDeltaFVarIds_3058_ = lean_ctor_get(v___x_3056_, 2);
v_postponed_3059_ = lean_ctor_get(v___x_3056_, 3);
v_diag_3060_ = lean_ctor_get(v___x_3056_, 4);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3056_, 1);
lean_dec(v_unused_3072_);
v___x_3062_ = v___x_3056_;
v_isShared_3063_ = v_isSharedCheck_3071_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_diag_3060_);
lean_inc(v_postponed_3059_);
lean_inc(v_zetaDeltaFVarIds_3058_);
lean_inc(v_mctx_3057_);
lean_dec(v___x_3056_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3071_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 1, v___x_2920_);
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_mctx_3057_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_2920_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_zetaDeltaFVarIds_3058_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_postponed_3059_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_diag_3060_);
v___x_3065_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
lean_object* v___x_3066_; lean_object* v___x_3068_; 
v___x_3066_ = lean_st_ref_put(v___y_2842_, v___x_3065_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3018_);
v___x_3068_ = v___x_3038_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3018_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2839_);
return v___x_3036_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3024_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
v_a_3081_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3025_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3025_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_a_3022_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
v_a_3089_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3023_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3023_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_dec(v_a_3011_);
lean_dec(v_a_3008_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
return v___x_3020_;
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_a_3011_);
lean_dec(v_a_3008_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
v_a_3097_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3016_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3016_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3008_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3105_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3010_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3010_);
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
lean_del_object(v___x_2943_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2854_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3113_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3007_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3007_);
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
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_del_object(v___x_2943_);
lean_dec(v_name_2941_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3121_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3000_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3000_);
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
lean_dec(v_a_2933_);
lean_dec_ref(v___x_2925_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec(v_a_2929_);
lean_dec_ref(v___x_2925_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3146_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_2930_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_2930_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v___x_2925_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3154_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_2928_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_2928_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec_ref(v___x_2925_);
lean_del_object(v___x_2892_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec_ref(v___x_2829_);
v_a_3162_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_2926_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_2926_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
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
lean_dec(v_a_2882_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_a_2877_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
v_a_3181_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_2878_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_2878_);
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
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
v_a_3189_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_2876_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_2876_);
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
lean_dec_ref(v___x_2867_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v___x_2864_);
lean_dec_ref(v___x_2862_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
v_a_3197_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_2870_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_2870_);
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
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_del_object(v___x_2854_);
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
lean_dec_ref(v___x_2828_);
lean_dec_ref(v___x_2827_);
lean_dec_ref(v___x_2823_);
lean_dec_ref(v___x_2819_);
v_a_3205_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_2857_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_2857_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_fs_2840_);
lean_dec(v_brecOnEqName_2839_);
lean_dec(v_brecOnName_2837_);
lean_dec(v___x_2836_);
lean_dec(v_levelParams_2835_);
lean_dec(v_brecOnGoName_2834_);
lean_dec_ref(v___x_2829_);
lean_dec_ref(v___x_2828_);
lean_dec_ref(v___x_2827_);
lean_dec_ref(v___x_2823_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2816_);
v_a_3215_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_2850_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_2850_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3223_ = _args[0];
lean_object* v_tail_3224_ = _args[1];
lean_object* v_recName_3225_ = _args[2];
lean_object* v___x_3226_ = _args[3];
lean_object* v___x_3227_ = _args[4];
lean_object* v___x_3228_ = _args[5];
lean_object* v___x_3229_ = _args[6];
lean_object* v___x_3230_ = _args[7];
lean_object* v_sz_3231_ = _args[8];
lean_object* v___x_3232_ = _args[9];
lean_object* v___x_3233_ = _args[10];
lean_object* v___x_3234_ = _args[11];
lean_object* v___x_3235_ = _args[12];
lean_object* v___x_3236_ = _args[13];
lean_object* v___x_3237_ = _args[14];
lean_object* v___x_3238_ = _args[15];
lean_object* v_val_3239_ = _args[16];
lean_object* v___x_3240_ = _args[17];
lean_object* v_brecOnGoName_3241_ = _args[18];
lean_object* v_levelParams_3242_ = _args[19];
lean_object* v___x_3243_ = _args[20];
lean_object* v_brecOnName_3244_ = _args[21];
lean_object* v___x_3245_ = _args[22];
lean_object* v_brecOnEqName_3246_ = _args[23];
lean_object* v_fs_3247_ = _args[24];
lean_object* v___y_3248_ = _args[25];
lean_object* v___y_3249_ = _args[26];
lean_object* v___y_3250_ = _args[27];
lean_object* v___y_3251_ = _args[28];
lean_object* v___y_3252_ = _args[29];
_start:
{
size_t v_sz_boxed_3253_; size_t v___x_30618__boxed_3254_; uint8_t v___x_30626__boxed_3255_; lean_object* v_res_3256_; 
v_sz_boxed_3253_ = lean_unbox_usize(v_sz_3231_);
lean_dec(v_sz_3231_);
v___x_30618__boxed_3254_ = lean_unbox_usize(v___x_3232_);
lean_dec(v___x_3232_);
v___x_30626__boxed_3255_ = lean_unbox(v___x_3240_);
v_res_3256_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3223_, v_tail_3224_, v_recName_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v___x_3230_, v_sz_boxed_3253_, v___x_30618__boxed_3254_, v___x_3233_, v___x_3234_, v___x_3235_, v___x_3236_, v___x_3237_, v___x_3238_, v_val_3239_, v___x_30626__boxed_3255_, v_brecOnGoName_3241_, v_levelParams_3242_, v___x_3243_, v_brecOnName_3244_, v___x_3245_, v_brecOnEqName_3246_, v_fs_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___x_3245_);
lean_dec(v_val_3239_);
lean_dec_ref(v___x_3238_);
lean_dec(v___x_3237_);
lean_dec_ref(v___x_3233_);
lean_dec(v___x_3229_);
lean_dec(v___x_3228_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3257_, lean_object* v_a_3258_, uint8_t v___x_3259_, lean_object* v_f_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; 
lean_inc_ref(v_targs_3257_);
v___x_3266_ = lean_array_push(v_targs_3257_, v_f_3260_);
v___x_3267_ = l_Lean_mkAppN(v_a_3258_, v_targs_3257_);
lean_dec_ref(v_targs_3257_);
v___x_3268_ = 0;
v___x_3269_ = 1;
v___x_3270_ = l_Lean_Meta_mkForallFVars(v___x_3266_, v___x_3267_, v___x_3268_, v___x_3259_, v___x_3259_, v___x_3269_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec_ref(v___x_3266_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3271_, lean_object* v_a_3272_, lean_object* v___x_3273_, lean_object* v_f_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
uint8_t v___x_31340__boxed_3280_; lean_object* v_res_3281_; 
v___x_31340__boxed_3280_ = lean_unbox(v___x_3273_);
v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3271_, v_a_3272_, v___x_31340__boxed_3280_, v_f_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3285_, uint8_t v___x_3286_, lean_object* v___x_3287_, lean_object* v_targs_3288_, lean_object* v_x_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; lean_object* v___f_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3295_ = lean_box(v___x_3286_);
lean_inc_ref(v_targs_3288_);
v___f_3296_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3296_, 0, v_targs_3288_);
lean_closure_set(v___f_3296_, 1, v_a_3285_);
lean_closure_set(v___f_3296_, 2, v___x_3295_);
v___x_3297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3298_ = l_Lean_mkAppN(v___x_3287_, v_targs_3288_);
lean_dec_ref(v_targs_3288_);
v___x_3299_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3297_, v___x_3298_, v___f_3296_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3300_, lean_object* v___x_3301_, lean_object* v___x_3302_, lean_object* v_targs_3303_, lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v___x_31374__boxed_3310_; lean_object* v_res_3311_; 
v___x_31374__boxed_3310_ = lean_unbox(v___x_3301_);
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3300_, v___x_31374__boxed_3310_, v___x_3302_, v_targs_3303_, v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec_ref(v_x_3304_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3312_, lean_object* v_x_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_a_3312_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3320_, v_x_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec_ref(v_x_3321_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; 
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_b_3334_);
return v___x_3341_;
}
else
{
lean_object* v_snd_3342_; lean_object* v_fst_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3440_; 
v_snd_3342_ = lean_ctor_get(v_b_3334_, 1);
v_fst_3343_ = lean_ctor_get(v_b_3334_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_b_3334_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3345_ = v_b_3334_;
v_isShared_3346_ = v_isSharedCheck_3440_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snd_3342_);
lean_inc(v_fst_3343_);
lean_dec(v_b_3334_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3440_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_fst_3347_; lean_object* v_snd_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3439_; 
v_fst_3347_ = lean_ctor_get(v_snd_3342_, 0);
v_snd_3348_ = lean_ctor_get(v_snd_3342_, 1);
v_isSharedCheck_3439_ = !lean_is_exclusive(v_snd_3342_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3350_ = v_snd_3342_;
v_isShared_3351_ = v_isSharedCheck_3439_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_snd_3348_);
lean_inc(v_fst_3347_);
lean_dec(v_snd_3342_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3439_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v_next_3360_; 
v_next_3360_ = lean_ctor_get(v_snd_3348_, 0);
lean_inc(v_next_3360_);
if (lean_obj_tag(v_next_3360_) == 0)
{
goto v___jp_3352_;
}
else
{
lean_object* v_upperBound_3361_; lean_object* v_val_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3438_; 
v_upperBound_3361_ = lean_ctor_get(v_snd_3348_, 1);
v_val_3362_ = lean_ctor_get(v_next_3360_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_next_3360_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3364_ = v_next_3360_;
v_isShared_3365_ = v_isSharedCheck_3438_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_val_3362_);
lean_dec(v_next_3360_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3438_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_nat_dec_lt(v_val_3362_, v_upperBound_3361_);
if (v___x_3366_ == 0)
{
lean_del_object(v___x_3364_);
lean_dec(v_val_3362_);
goto v___jp_3352_;
}
else
{
lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3435_; 
lean_inc(v_upperBound_3361_);
lean_del_object(v___x_3350_);
lean_del_object(v___x_3345_);
v_isSharedCheck_3435_ = !lean_is_exclusive(v_snd_3348_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3436_ = lean_ctor_get(v_snd_3348_, 1);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_snd_3348_, 0);
lean_dec(v_unused_3437_);
v___x_3368_ = v_snd_3348_;
v_isShared_3369_ = v_isSharedCheck_3435_;
goto v_resetjp_3367_;
}
else
{
lean_dec(v_snd_3348_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3435_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v_array_3370_; lean_object* v_start_3371_; lean_object* v_stop_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; 
v_array_3370_ = lean_ctor_get(v_fst_3347_, 0);
v_start_3371_ = lean_ctor_get(v_fst_3347_, 1);
v_stop_3372_ = lean_ctor_get(v_fst_3347_, 2);
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_add(v_val_3362_, v___x_3373_);
lean_dec(v_val_3362_);
lean_inc(v___x_3374_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3374_);
v___x_3376_ = v___x_3364_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
lean_object* v___x_3378_; 
if (v_isShared_3369_ == 0)
{
lean_ctor_set(v___x_3368_, 0, v___x_3376_);
v___x_3378_ = v___x_3368_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_upperBound_3361_);
v___x_3378_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_nat_dec_lt(v_start_3371_, v_stop_3372_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_dec(v___x_3374_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_fst_3347_);
lean_ctor_set(v___x_3380_, 1, v___x_3378_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_fst_3343_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3381_);
return v___x_3382_;
}
else
{
lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3429_; 
lean_inc(v_stop_3372_);
lean_inc(v_start_3371_);
lean_inc_ref(v_array_3370_);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_fst_3347_);
if (v_isSharedCheck_3429_ == 0)
{
lean_object* v_unused_3430_; lean_object* v_unused_3431_; lean_object* v_unused_3432_; 
v_unused_3430_ = lean_ctor_get(v_fst_3347_, 2);
lean_dec(v_unused_3430_);
v_unused_3431_ = lean_ctor_get(v_fst_3347_, 1);
lean_dec(v_unused_3431_);
v_unused_3432_ = lean_ctor_get(v_fst_3347_, 0);
lean_dec(v_unused_3432_);
v___x_3384_ = v_fst_3347_;
v_isShared_3385_ = v_isSharedCheck_3429_;
goto v_resetjp_3383_;
}
else
{
lean_dec(v_fst_3347_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3429_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_a_3386_; lean_object* v___x_3387_; 
v_a_3386_ = lean_array_uget_borrowed(v_as_3331_, v_i_3333_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v_a_3386_);
v___x_3387_ = lean_infer_type(v_a_3386_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___f_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = lean_nat_dec_lt(v___x_3329_, v___x_3330_);
v___x_3390_ = lean_array_fget_borrowed(v_array_3370_, v_start_3371_);
v___x_3391_ = lean_box(v___x_3389_);
lean_inc(v___x_3390_);
lean_inc(v_a_3386_);
v___f_3392_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3392_, 0, v_a_3386_);
lean_closure_set(v___f_3392_, 1, v___x_3391_);
lean_closure_set(v___f_3392_, 2, v___x_3390_);
v___x_3393_ = 0;
v___x_3394_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3388_, v___f_3392_, v___x_3393_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___f_3396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3396_, 0, v_a_3395_);
v___x_3397_ = lean_nat_add(v_start_3371_, v___x_3373_);
lean_dec(v_start_3371_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 1, v___x_3397_);
v___x_3399_ = v___x_3384_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_array_3370_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3412_, 2, v_stop_3372_);
v___x_3399_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; size_t v___x_3409_; size_t v___x_3410_; 
v___x_3400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3401_ = l_Nat_reprFast(v___x_3374_);
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
lean_dec_ref(v___x_3401_);
v___x_3403_ = lean_box(0);
v___x_3404_ = l_Lean_Name_str___override(v___x_3403_, v___x_3402_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v___f_3396_);
v___x_3406_ = lean_array_push(v_fst_3343_, v___x_3405_);
v___x_3407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3399_);
lean_ctor_set(v___x_3407_, 1, v___x_3378_);
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = ((size_t)1ULL);
v___x_3410_ = lean_usize_add(v_i_3333_, v___x_3409_);
v_i_3333_ = v___x_3410_;
v_b_3334_ = v___x_3408_;
goto _start;
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_del_object(v___x_3384_);
lean_dec_ref(v___x_3378_);
lean_dec(v___x_3374_);
lean_dec(v_stop_3372_);
lean_dec(v_start_3371_);
lean_dec_ref(v_array_3370_);
lean_dec(v_fst_3343_);
v_a_3413_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3394_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3394_);
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
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3384_);
lean_dec_ref(v___x_3378_);
lean_dec(v___x_3374_);
lean_dec(v_stop_3372_);
lean_dec(v_start_3371_);
lean_dec_ref(v_array_3370_);
lean_dec(v_fst_3343_);
v_a_3421_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3387_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3387_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
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
v___jp_3352_:
{
lean_object* v___x_3354_; 
if (v_isShared_3351_ == 0)
{
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_fst_3347_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_snd_3348_);
v___x_3354_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
lean_object* v___x_3356_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3354_);
v___x_3356_ = v___x_3345_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_fst_3343_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v_as_3443_, lean_object* v_sz_3444_, lean_object* v_i_3445_, lean_object* v_b_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
size_t v_sz_boxed_3452_; size_t v_i_boxed_3453_; lean_object* v_res_3454_; 
v_sz_boxed_3452_ = lean_unbox_usize(v_sz_3444_);
lean_dec(v_sz_3444_);
v_i_boxed_3453_ = lean_unbox_usize(v_i_3445_);
lean_dec(v_i_3445_);
v_res_3454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3441_, v___x_3442_, v_as_3443_, v_sz_boxed_3452_, v_i_boxed_3453_, v_b_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec_ref(v_as_3443_);
lean_dec(v___x_3442_);
lean_dec(v___x_3441_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3455_, size_t v_i_3456_, lean_object* v_bs_3457_){
_start:
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_usize_dec_lt(v_i_3456_, v_sz_3455_);
if (v___x_3458_ == 0)
{
return v_bs_3457_;
}
else
{
lean_object* v_v_3459_; lean_object* v_fst_3460_; lean_object* v_snd_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3477_; 
v_v_3459_ = lean_array_uget(v_bs_3457_, v_i_3456_);
v_fst_3460_ = lean_ctor_get(v_v_3459_, 0);
v_snd_3461_ = lean_ctor_get(v_v_3459_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_v_3459_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3463_ = v_v_3459_;
v_isShared_3464_ = v_isSharedCheck_3477_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_snd_3461_);
lean_inc(v_fst_3460_);
lean_dec(v_v_3459_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3477_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3465_; lean_object* v_bs_x27_3466_; uint8_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3465_ = lean_unsigned_to_nat(0u);
v_bs_x27_3466_ = lean_array_uset(v_bs_3457_, v_i_3456_, v___x_3465_);
v___x_3467_ = 0;
v___x_3468_ = lean_box(v___x_3467_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3468_);
v___x_3470_ = v___x_3463_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3468_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_snd_3461_);
v___x_3470_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; size_t v___x_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
v___x_3471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3471_, 0, v_fst_3460_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = ((size_t)1ULL);
v___x_3473_ = lean_usize_add(v_i_3456_, v___x_3472_);
v___x_3474_ = lean_array_uset(v_bs_x27_3466_, v_i_3456_, v___x_3471_);
v_i_3456_ = v___x_3473_;
v_bs_3457_ = v___x_3474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3478_, lean_object* v_i_3479_, lean_object* v_bs_3480_){
_start:
{
size_t v_sz_boxed_3481_; size_t v_i_boxed_3482_; lean_object* v_res_3483_; 
v_sz_boxed_3481_ = lean_unbox_usize(v_sz_3478_);
lean_dec(v_sz_3478_);
v_i_boxed_3482_ = lean_unbox_usize(v_i_3479_);
lean_dec(v_i_3479_);
v_res_3483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3481_, v_i_boxed_3482_, v_bs_3480_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3484_, lean_object* v___x_3485_, lean_object* v_a_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_30168__overap_3492_; lean_object* v___x_3493_; 
v___x_30168__overap_3492_ = l_instInhabitedOfMonad___redArg(v___x_3484_, v___x_3485_);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
lean_inc(v___y_3488_);
lean_inc_ref(v___y_3487_);
v___x_3493_ = lean_apply_5(v___x_30168__overap_3492_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, lean_box(0));
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3494_, lean_object* v___x_3495_, lean_object* v_a_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3494_, v___x_3495_, v_a_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec_ref(v_a_3496_);
return v_res_3502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_instMonadEIO(lean_box(0));
return v___x_3503_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3505_ = l_StateRefT_x27_instMonad___redArg(v___x_3504_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3510_, lean_object* v_declInfos_3511_, lean_object* v_k_3512_, lean_object* v_kind_3513_, lean_object* v_b_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
uint8_t v_kind_boxed_3520_; lean_object* v_res_3521_; 
v_kind_boxed_3520_ = lean_unbox(v_kind_3513_);
v_res_3521_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3510_, v_declInfos_3511_, v_k_3512_, v_kind_boxed_3520_, v_b_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3522_, lean_object* v_declInfos_3523_, lean_object* v_k_3524_, uint8_t v_kind_3525_, lean_object* v_name_3526_, uint8_t v_bi_3527_, lean_object* v_type_3528_, uint8_t v_kind_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; lean_object* v___f_3536_; lean_object* v___x_3537_; 
v___x_3535_ = lean_box(v_kind_3525_);
v___f_3536_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3536_, 0, v_acc_3522_);
lean_closure_set(v___f_3536_, 1, v_declInfos_3523_);
lean_closure_set(v___f_3536_, 2, v_k_3524_);
lean_closure_set(v___f_3536_, 3, v___x_3535_);
v___x_3537_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3526_, v_bi_3527_, v_type_3528_, v___f_3536_, v_kind_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3537_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3537_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_a_3546_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3537_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3537_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3554_, lean_object* v_k_3555_, uint8_t v_kind_3556_, lean_object* v_acc_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; lean_object* v_toApplicative_3564_; lean_object* v_toFunctor_3565_; lean_object* v_toSeq_3566_; lean_object* v_toSeqLeft_3567_; lean_object* v_toSeqRight_3568_; lean_object* v___f_3569_; lean_object* v___f_3570_; lean_object* v___f_3571_; lean_object* v___f_3572_; lean_object* v___x_3573_; lean_object* v___f_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v_toApplicative_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3636_; 
v___x_3563_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3564_ = lean_ctor_get(v___x_3563_, 0);
v_toFunctor_3565_ = lean_ctor_get(v_toApplicative_3564_, 0);
v_toSeq_3566_ = lean_ctor_get(v_toApplicative_3564_, 2);
v_toSeqLeft_3567_ = lean_ctor_get(v_toApplicative_3564_, 3);
v_toSeqRight_3568_ = lean_ctor_get(v_toApplicative_3564_, 4);
v___f_3569_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3570_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3565_, 2);
v___f_3571_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3571_, 0, v_toFunctor_3565_);
v___f_3572_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3572_, 0, v_toFunctor_3565_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___f_3571_);
lean_ctor_set(v___x_3573_, 1, v___f_3572_);
lean_inc(v_toSeqRight_3568_);
v___f_3574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3574_, 0, v_toSeqRight_3568_);
lean_inc(v_toSeqLeft_3567_);
v___f_3575_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3575_, 0, v_toSeqLeft_3567_);
lean_inc(v_toSeq_3566_);
v___f_3576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3576_, 0, v_toSeq_3566_);
v___x_3577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3573_);
lean_ctor_set(v___x_3577_, 1, v___f_3569_);
lean_ctor_set(v___x_3577_, 2, v___f_3576_);
lean_ctor_set(v___x_3577_, 3, v___f_3575_);
lean_ctor_set(v___x_3577_, 4, v___f_3574_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___f_3570_);
v___x_3579_ = l_StateRefT_x27_instMonad___redArg(v___x_3578_);
v_toApplicative_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3579_, 1);
lean_dec(v_unused_3637_);
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3636_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_toApplicative_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3636_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v_toFunctor_3584_; lean_object* v_toSeq_3585_; lean_object* v_toSeqLeft_3586_; lean_object* v_toSeqRight_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3634_; 
v_toFunctor_3584_ = lean_ctor_get(v_toApplicative_3580_, 0);
v_toSeq_3585_ = lean_ctor_get(v_toApplicative_3580_, 2);
v_toSeqLeft_3586_ = lean_ctor_get(v_toApplicative_3580_, 3);
v_toSeqRight_3587_ = lean_ctor_get(v_toApplicative_3580_, 4);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_toApplicative_3580_);
if (v_isSharedCheck_3634_ == 0)
{
lean_object* v_unused_3635_; 
v_unused_3635_ = lean_ctor_get(v_toApplicative_3580_, 1);
lean_dec(v_unused_3635_);
v___x_3589_ = v_toApplicative_3580_;
v_isShared_3590_ = v_isSharedCheck_3634_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_toSeqRight_3587_);
lean_inc(v_toSeqLeft_3586_);
lean_inc(v_toSeq_3585_);
lean_inc(v_toFunctor_3584_);
lean_dec(v_toApplicative_3580_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3634_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___f_3594_; lean_object* v___x_3595_; lean_object* v___f_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___x_3600_; 
v___f_3591_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3592_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3584_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toFunctor_3584_);
v___f_3594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3594_, 0, v_toFunctor_3584_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___f_3593_);
lean_ctor_set(v___x_3595_, 1, v___f_3594_);
v___f_3596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3596_, 0, v_toSeqRight_3587_);
v___f_3597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3597_, 0, v_toSeqLeft_3586_);
v___f_3598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3598_, 0, v_toSeq_3585_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 4, v___f_3596_);
lean_ctor_set(v___x_3589_, 3, v___f_3597_);
lean_ctor_set(v___x_3589_, 2, v___f_3598_);
lean_ctor_set(v___x_3589_, 1, v___f_3591_);
lean_ctor_set(v___x_3589_, 0, v___x_3595_);
v___x_3600_ = v___x_3589_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___f_3591_);
lean_ctor_set(v_reuseFailAlloc_3633_, 2, v___f_3598_);
lean_ctor_set(v_reuseFailAlloc_3633_, 3, v___f_3597_);
lean_ctor_set(v_reuseFailAlloc_3633_, 4, v___f_3596_);
v___x_3600_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3583_ == 0)
{
lean_ctor_set(v___x_3582_, 1, v___f_3592_);
lean_ctor_set(v___x_3582_, 0, v___x_3600_);
v___x_3602_ = v___x_3582_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3600_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v___f_3592_);
v___x_3602_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3603_ = lean_array_get_size(v_acc_3557_);
v___x_3604_ = lean_array_get_size(v_declInfos_3554_);
v___x_3605_ = lean_nat_dec_lt(v___x_3603_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; 
lean_dec_ref(v___x_3602_);
lean_dec_ref(v_declInfos_3554_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
v___x_3606_ = lean_apply_6(v_k_3555_, v_acc_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, lean_box(0));
return v___x_3606_;
}
else
{
lean_object* v___x_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_snd_3616_; lean_object* v_fst_3617_; lean_object* v_fst_3618_; lean_object* v_snd_3619_; lean_object* v___x_3620_; 
v___x_3607_ = lean_box(0);
v___x_3608_ = 0;
v___x_3609_ = l_Lean_instInhabitedExpr;
v___f_3610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3610_, 0, v___x_3602_);
lean_closure_set(v___f_3610_, 1, v___x_3609_);
v___f_3611_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3611_, 0, v___f_3610_);
v___x_3612_ = lean_box(v___x_3608_);
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___f_3611_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3607_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_array_get(v___x_3614_, v_declInfos_3554_, v___x_3603_);
lean_dec_ref_known(v___x_3614_, 2);
v_snd_3616_ = lean_ctor_get(v___x_3615_, 1);
lean_inc(v_snd_3616_);
v_fst_3617_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_fst_3617_);
lean_dec(v___x_3615_);
v_fst_3618_ = lean_ctor_get(v_snd_3616_, 0);
lean_inc(v_fst_3618_);
v_snd_3619_ = lean_ctor_get(v_snd_3616_, 1);
lean_inc(v_snd_3619_);
lean_dec(v_snd_3616_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc_ref(v___y_3558_);
lean_inc_ref(v_acc_3557_);
v___x_3620_ = lean_apply_6(v_snd_3619_, v_acc_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, lean_box(0));
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v___x_3622_ = lean_unbox(v_fst_3618_);
lean_dec(v_fst_3618_);
v___x_3623_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3557_, v_declInfos_3554_, v_k_3555_, v_kind_3556_, v_fst_3617_, v___x_3622_, v_a_3621_, v_kind_3556_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
return v___x_3623_;
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_fst_3618_);
lean_dec(v_fst_3617_);
lean_dec_ref(v_acc_3557_);
lean_dec_ref(v_k_3555_);
lean_dec_ref(v_declInfos_3554_);
v_a_3624_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3620_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3620_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3638_, lean_object* v_declInfos_3639_, lean_object* v_k_3640_, uint8_t v_kind_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_array_push(v_acc_3638_, v_b_3642_);
v___x_3649_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3639_, v_k_3640_, v_kind_3641_, v___x_3648_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3650_, lean_object* v_declInfos_3651_, lean_object* v_k_3652_, lean_object* v_kind_3653_, lean_object* v_name_3654_, lean_object* v_bi_3655_, lean_object* v_type_3656_, lean_object* v_kind_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v_kind_boxed_3663_; uint8_t v_bi_boxed_3664_; uint8_t v_kind_boxed_3665_; lean_object* v_res_3666_; 
v_kind_boxed_3663_ = lean_unbox(v_kind_3653_);
v_bi_boxed_3664_ = lean_unbox(v_bi_3655_);
v_kind_boxed_3665_ = lean_unbox(v_kind_3657_);
v_res_3666_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3650_, v_declInfos_3651_, v_k_3652_, v_kind_boxed_3663_, v_name_3654_, v_bi_boxed_3664_, v_type_3656_, v_kind_boxed_3665_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3667_, lean_object* v_k_3668_, lean_object* v_kind_3669_, lean_object* v_acc_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_kind_boxed_3676_; lean_object* v_res_3677_; 
v_kind_boxed_3676_ = lean_unbox(v_kind_3669_);
v_res_3677_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3667_, v_k_3668_, v_kind_boxed_3676_, v_acc_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3678_, lean_object* v_k_3679_, uint8_t v_kind_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3687_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3678_, v_k_3679_, v_kind_3680_, v___x_3686_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3688_, lean_object* v_k_3689_, lean_object* v_kind_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
uint8_t v_kind_boxed_3696_; lean_object* v_res_3697_; 
v_kind_boxed_3696_ = lean_unbox(v_kind_3690_);
v_res_3697_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3688_, v_k_3689_, v_kind_boxed_3696_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3698_, lean_object* v_k_3699_, uint8_t v_kind_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
size_t v_sz_3706_; size_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v_sz_3706_ = lean_array_size(v_declInfos_3698_);
v___x_3707_ = ((size_t)0ULL);
v___x_3708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3706_, v___x_3707_, v_declInfos_3698_);
v___x_3709_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3708_, v_k_3699_, v_kind_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3710_, lean_object* v_k_3711_, lean_object* v_kind_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v_kind_boxed_3718_; lean_object* v_res_3719_; 
v_kind_boxed_3718_ = lean_unbox(v_kind_3712_);
v_res_3719_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3710_, v_k_3711_, v_kind_boxed_3718_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3721_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3722_ = lean_unsigned_to_nat(4u);
v___x_3723_ = lean_unsigned_to_nat(202u);
v___x_3724_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3725_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3726_ = l_mkPanicMessageWithDecl(v___x_3725_, v___x_3724_, v___x_3723_, v___x_3722_, v___x_3721_);
return v___x_3726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3733_ = l_Lean_stringToMessageData(v___x_3732_);
return v___x_3733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3735_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3736_ = l_Lean_stringToMessageData(v___x_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3739_, lean_object* v_numMotives_3740_, lean_object* v_numMinors_3741_, lean_object* v___x_3742_, lean_object* v___x_3743_, lean_object* v_all_3744_, lean_object* v___x_3745_, lean_object* v_head_3746_, lean_object* v_tail_3747_, lean_object* v_recName_3748_, lean_object* v_brecOnGoName_3749_, lean_object* v_levelParams_3750_, lean_object* v_brecOnName_3751_, lean_object* v_brecOnEqName_3752_, lean_object* v_type_3753_, lean_object* v_refArgs_3754_, lean_object* v_refBody_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3761_ = lean_nat_add(v_nParams_3739_, v_numMotives_3740_);
v___x_3762_ = lean_nat_add(v___x_3761_, v_numMinors_3741_);
v___x_3763_ = lean_array_get_size(v_refArgs_3754_);
v___x_3764_ = lean_nat_dec_lt(v___x_3762_, v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec_ref(v_type_3753_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
lean_dec(v_nParams_3739_);
v___x_3765_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3766_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3765_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3766_;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3767_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3739_);
lean_inc_ref_n(v_refArgs_3754_, 2);
v___x_3768_ = l_Array_toSubarray___redArg(v_refArgs_3754_, v___x_3767_, v_nParams_3739_);
lean_inc(v___x_3761_);
v___x_3769_ = l_Array_toSubarray___redArg(v_refArgs_3754_, v_nParams_3739_, v___x_3761_);
v___x_3770_ = l_Subarray_copy___redArg(v___x_3769_);
v___x_3771_ = l_Lean_Expr_getAppFn(v_refBody_3755_);
v___x_3772_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3770_, v___x_3771_);
lean_dec_ref(v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 1)
{
lean_object* v_val_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec_ref(v_type_3753_);
v_val_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_val_3773_);
lean_dec_ref_known(v___x_3772_, 1);
v___x_3774_ = lean_unsigned_to_nat(1u);
v___x_3775_ = lean_nat_sub(v___x_3763_, v___x_3774_);
v___x_3776_ = lean_array_get(v___x_3742_, v_refArgs_3754_, v___x_3775_);
lean_inc(v___y_3759_);
lean_inc_ref(v___y_3758_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___x_3776_);
v___x_3777_ = lean_infer_type(v___x_3776_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
lean_inc(v___y_3759_);
lean_inc_ref(v___y_3758_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
v___x_3779_ = lean_infer_type(v_a_3778_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3780_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
if (lean_obj_tag(v_a_3782_) == 1)
{
lean_object* v_val_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; size_t v_sz_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v_val_3783_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v_a_3782_, 1);
lean_inc(v___x_3762_);
lean_inc_ref(v_refArgs_3754_);
v___x_3784_ = l_Array_toSubarray___redArg(v_refArgs_3754_, v___x_3761_, v___x_3762_);
v___x_3785_ = l_Subarray_copy___redArg(v___x_3768_);
lean_inc_ref(v___x_3770_);
lean_inc_ref(v___x_3785_);
lean_inc(v___x_3743_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3786_, 0, v___x_3743_);
lean_closure_set(v___f_3786_, 1, v___x_3785_);
lean_closure_set(v___f_3786_, 2, v___x_3770_);
lean_closure_set(v___f_3786_, 3, v_all_3744_);
lean_closure_set(v___f_3786_, 4, v___x_3745_);
lean_closure_set(v___f_3786_, 5, v___x_3767_);
lean_closure_set(v___f_3786_, 6, v___x_3774_);
v___x_3787_ = lean_array_get_size(v___x_3770_);
v___x_3788_ = l_Array_ofFn___redArg(v___x_3787_, v___f_3786_);
v___x_3789_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3790_ = lean_array_get_size(v___x_3788_);
lean_inc_ref(v___x_3788_);
v___x_3791_ = l_Array_toSubarray___redArg(v___x_3788_, v___x_3767_, v___x_3790_);
v___x_3792_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set(v___x_3793_, 1, v___x_3787_);
lean_inc_ref(v___x_3791_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3791_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3789_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v_sz_3796_ = lean_array_size(v___x_3770_);
v___x_3797_ = ((size_t)0ULL);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3762_, v___x_3763_, v___x_3770_, v_sz_3796_, v___x_3797_, v___x_3795_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v_fst_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v_fst_3800_ = lean_ctor_get(v_a_3799_, 0);
lean_inc(v_fst_3800_);
lean_dec(v_a_3799_);
v___x_3801_ = l_Subarray_copy___redArg(v___x_3784_);
lean_inc(v___x_3762_);
v___x_3802_ = l_Array_toSubarray___redArg(v_refArgs_3754_, v___x_3762_, v___x_3775_);
v___x_3803_ = l_Subarray_copy___redArg(v___x_3802_);
v___x_3804_ = l_Lean_mkLevelMax(v_val_3783_, v_head_3746_);
v___x_3805_ = lean_box_usize(v_sz_3796_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3807_ = lean_box(v___x_3764_);
v___f_3808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 30, 24);
lean_closure_set(v___f_3808_, 0, v___x_3804_);
lean_closure_set(v___f_3808_, 1, v_tail_3747_);
lean_closure_set(v___f_3808_, 2, v_recName_3748_);
lean_closure_set(v___f_3808_, 3, v___x_3785_);
lean_closure_set(v___f_3808_, 4, v___x_3791_);
lean_closure_set(v___f_3808_, 5, v___x_3762_);
lean_closure_set(v___f_3808_, 6, v___x_3763_);
lean_closure_set(v___f_3808_, 7, v___x_3770_);
lean_closure_set(v___f_3808_, 8, v___x_3805_);
lean_closure_set(v___f_3808_, 9, v___x_3806_);
lean_closure_set(v___f_3808_, 10, v___x_3801_);
lean_closure_set(v___f_3808_, 11, v___x_3788_);
lean_closure_set(v___f_3808_, 12, v___x_3803_);
lean_closure_set(v___f_3808_, 13, v___x_3776_);
lean_closure_set(v___f_3808_, 14, v___x_3774_);
lean_closure_set(v___f_3808_, 15, v___x_3742_);
lean_closure_set(v___f_3808_, 16, v_val_3773_);
lean_closure_set(v___f_3808_, 17, v___x_3807_);
lean_closure_set(v___f_3808_, 18, v_brecOnGoName_3749_);
lean_closure_set(v___f_3808_, 19, v_levelParams_3750_);
lean_closure_set(v___f_3808_, 20, v___x_3743_);
lean_closure_set(v___f_3808_, 21, v_brecOnName_3751_);
lean_closure_set(v___f_3808_, 22, v___x_3767_);
lean_closure_set(v___f_3808_, 23, v_brecOnEqName_3752_);
v___x_3809_ = 0;
v___x_3810_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3800_, v___f_3808_, v___x_3809_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3810_;
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v___x_3791_);
lean_dec_ref(v___x_3788_);
lean_dec_ref(v___x_3785_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3783_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3773_);
lean_dec_ref(v___x_3770_);
lean_dec(v___x_3762_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v_a_3811_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3798_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3798_);
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
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
lean_dec(v_a_3782_);
lean_dec(v___x_3775_);
lean_dec(v_val_3773_);
lean_dec_ref(v___x_3770_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3820_ = l_Lean_MessageData_ofExpr(v___x_3776_);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3823_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3824_;
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3773_);
lean_dec_ref(v___x_3770_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v_a_3825_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3781_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3781_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3773_);
lean_dec_ref(v___x_3770_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v_a_3833_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3779_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3779_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3773_);
lean_dec_ref(v___x_3770_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v_a_3841_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3777_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3777_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
lean_dec(v___x_3772_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3762_);
lean_dec(v___x_3761_);
lean_dec_ref(v_refArgs_3754_);
lean_dec(v_brecOnEqName_3752_);
lean_dec(v_brecOnName_3751_);
lean_dec(v_levelParams_3750_);
lean_dec(v_brecOnGoName_3749_);
lean_dec(v_recName_3748_);
lean_dec(v_tail_3747_);
lean_dec(v_head_3746_);
lean_dec(v___x_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec_ref(v___x_3742_);
v___x_3849_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3850_ = l_Lean_MessageData_ofExpr(v_type_3753_);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_array_to_list(v___x_3770_);
v___x_3855_ = lean_box(0);
v___x_3856_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3854_, v___x_3855_);
v___x_3857_ = l_Lean_MessageData_ofList(v___x_3856_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3853_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3858_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3859_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3860_ = _args[0];
lean_object* v_numMotives_3861_ = _args[1];
lean_object* v_numMinors_3862_ = _args[2];
lean_object* v___x_3863_ = _args[3];
lean_object* v___x_3864_ = _args[4];
lean_object* v_all_3865_ = _args[5];
lean_object* v___x_3866_ = _args[6];
lean_object* v_head_3867_ = _args[7];
lean_object* v_tail_3868_ = _args[8];
lean_object* v_recName_3869_ = _args[9];
lean_object* v_brecOnGoName_3870_ = _args[10];
lean_object* v_levelParams_3871_ = _args[11];
lean_object* v_brecOnName_3872_ = _args[12];
lean_object* v_brecOnEqName_3873_ = _args[13];
lean_object* v_type_3874_ = _args[14];
lean_object* v_refArgs_3875_ = _args[15];
lean_object* v_refBody_3876_ = _args[16];
lean_object* v___y_3877_ = _args[17];
lean_object* v___y_3878_ = _args[18];
lean_object* v___y_3879_ = _args[19];
lean_object* v___y_3880_ = _args[20];
lean_object* v___y_3881_ = _args[21];
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3860_, v_numMotives_3861_, v_numMinors_3862_, v___x_3863_, v___x_3864_, v_all_3865_, v___x_3866_, v_head_3867_, v_tail_3868_, v_recName_3869_, v_brecOnGoName_3870_, v_levelParams_3871_, v_brecOnName_3872_, v_brecOnEqName_3873_, v_type_3874_, v_refArgs_3875_, v_refBody_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec_ref(v_refBody_3876_);
lean_dec(v_numMinors_3862_);
lean_dec(v_numMotives_3861_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3885_, lean_object* v_nParams_3886_, lean_object* v_all_3887_, lean_object* v_brecOnName_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3894_; 
lean_inc(v_recName_3885_);
v___x_3894_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3885_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3928_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3928_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3928_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
if (lean_obj_tag(v_a_3895_) == 7)
{
lean_object* v_val_3899_; lean_object* v_toConstantVal_3900_; lean_object* v_numMotives_3901_; lean_object* v_numMinors_3902_; lean_object* v_levelParams_3903_; lean_object* v_type_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_del_object(v___x_3897_);
v_val_3899_ = lean_ctor_get(v_a_3895_, 0);
lean_inc_ref(v_val_3899_);
lean_dec_ref_known(v_a_3895_, 1);
v_toConstantVal_3900_ = lean_ctor_get(v_val_3899_, 0);
lean_inc_ref(v_toConstantVal_3900_);
v_numMotives_3901_ = lean_ctor_get(v_val_3899_, 4);
lean_inc(v_numMotives_3901_);
v_numMinors_3902_ = lean_ctor_get(v_val_3899_, 5);
lean_inc(v_numMinors_3902_);
lean_dec_ref(v_val_3899_);
v_levelParams_3903_ = lean_ctor_get(v_toConstantVal_3900_, 1);
lean_inc_n(v_levelParams_3903_, 2);
v_type_3904_ = lean_ctor_get(v_toConstantVal_3900_, 2);
lean_inc_ref(v_type_3904_);
lean_dec_ref(v_toConstantVal_3900_);
v___x_3905_ = lean_box(0);
v___x_3906_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3903_, v___x_3905_);
if (lean_obj_tag(v___x_3906_) == 1)
{
lean_object* v_head_3907_; lean_object* v_tail_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v_brecOnGoName_3912_; lean_object* v___x_3913_; lean_object* v_brecOnEqName_3914_; lean_object* v___f_3915_; uint8_t v___x_3916_; lean_object* v___x_3917_; 
v_head_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_head_3907_);
v_tail_3908_ = lean_ctor_get(v___x_3906_, 1);
lean_inc(v_tail_3908_);
v___x_3909_ = l_Lean_instInhabitedExpr;
v___x_3910_ = lean_box(0);
v___x_3911_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3888_, 2);
v_brecOnGoName_3912_ = l_Lean_Name_str___override(v_brecOnName_3888_, v___x_3911_);
v___x_3913_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3914_ = l_Lean_Name_str___override(v_brecOnName_3888_, v___x_3913_);
lean_inc_ref(v_type_3904_);
v___f_3915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3915_, 0, v_nParams_3886_);
lean_closure_set(v___f_3915_, 1, v_numMotives_3901_);
lean_closure_set(v___f_3915_, 2, v_numMinors_3902_);
lean_closure_set(v___f_3915_, 3, v___x_3909_);
lean_closure_set(v___f_3915_, 4, v___x_3906_);
lean_closure_set(v___f_3915_, 5, v_all_3887_);
lean_closure_set(v___f_3915_, 6, v___x_3910_);
lean_closure_set(v___f_3915_, 7, v_head_3907_);
lean_closure_set(v___f_3915_, 8, v_tail_3908_);
lean_closure_set(v___f_3915_, 9, v_recName_3885_);
lean_closure_set(v___f_3915_, 10, v_brecOnGoName_3912_);
lean_closure_set(v___f_3915_, 11, v_levelParams_3903_);
lean_closure_set(v___f_3915_, 12, v_brecOnName_3888_);
lean_closure_set(v___f_3915_, 13, v_brecOnEqName_3914_);
lean_closure_set(v___f_3915_, 14, v_type_3904_);
v___x_3916_ = 0;
v___x_3917_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3904_, v___f_3915_, v___x_3916_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
return v___x_3917_;
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec(v___x_3906_);
lean_dec_ref(v_type_3904_);
lean_dec(v_levelParams_3903_);
lean_dec(v_numMinors_3902_);
lean_dec(v_numMotives_3901_);
lean_dec(v_brecOnName_3888_);
lean_dec_ref(v_all_3887_);
lean_dec(v_nParams_3886_);
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3919_ = l_Lean_MessageData_ofName(v_recName_3885_);
v___x_3920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3920_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3922_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
return v___x_3923_;
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec(v_a_3895_);
lean_dec(v_brecOnName_3888_);
lean_dec_ref(v_all_3887_);
lean_dec(v_nParams_3886_);
lean_dec(v_recName_3885_);
v___x_3924_ = lean_box(0);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3924_);
v___x_3926_ = v___x_3897_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
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
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_brecOnName_3888_);
lean_dec_ref(v_all_3887_);
lean_dec(v_nParams_3886_);
lean_dec(v_recName_3885_);
v_a_3929_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3894_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3894_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3937_, lean_object* v_nParams_3938_, lean_object* v_all_3939_, lean_object* v_brecOnName_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3937_, v_nParams_3938_, v_all_3939_, v_brecOnName_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_a_3943_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v___x_3950_, lean_object* v___x_3951_, lean_object* v_a_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v___x_3959_; 
v___x_3959_ = lean_nat_dec_lt(v_a_3952_, v_upperBound_3947_);
if (v___x_3959_ == 0)
{
lean_object* v___x_3960_; 
lean_dec(v_a_3952_);
lean_dec_ref(v___x_3951_);
lean_dec(v___x_3950_);
lean_dec(v___x_3949_);
lean_dec(v___x_3948_);
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v_b_3953_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3961_ = lean_unsigned_to_nat(1u);
v___x_3962_ = lean_nat_add(v_a_3952_, v___x_3961_);
lean_dec(v_a_3952_);
lean_inc_n(v___x_3962_, 2);
lean_inc(v___x_3948_);
v___x_3963_ = lean_name_append_index_after(v___x_3948_, v___x_3962_);
lean_inc(v___x_3949_);
v___x_3964_ = lean_name_append_index_after(v___x_3949_, v___x_3962_);
lean_inc_ref(v___x_3951_);
lean_inc(v___x_3950_);
v___x_3965_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3963_, v___x_3950_, v___x_3951_, v___x_3964_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v___x_3966_; 
lean_dec_ref_known(v___x_3965_, 1);
v___x_3966_ = lean_box(0);
v_a_3952_ = v___x_3962_;
v_b_3953_ = v___x_3966_;
goto _start;
}
else
{
lean_dec(v___x_3962_);
lean_dec_ref(v___x_3951_);
lean_dec(v___x_3950_);
lean_dec(v___x_3949_);
lean_dec(v___x_3948_);
return v___x_3965_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v___x_3972_, lean_object* v_a_3973_, lean_object* v_b_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3968_, v___x_3969_, v___x_3970_, v___x_3971_, v___x_3972_, v_a_3973_, v_b_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v_upperBound_3968_);
return v_res_3980_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3986_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3987_ = l_Lean_Name_append(v___x_3986_, v___x_3985_);
return v___x_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_){
_start:
{
lean_object* v_options_3994_; lean_object* v_toCold_3995_; uint8_t v_hasTrace_3996_; lean_object* v___x_3997_; 
v_options_3994_ = lean_ctor_get(v_a_3991_, 1);
v_toCold_3995_ = lean_ctor_get(v_a_3991_, 0);
v_hasTrace_3996_ = lean_ctor_get_uint8(v_options_3994_, sizeof(void*)*1);
v___x_3997_ = lean_box(0);
if (v_hasTrace_3996_ == 0)
{
lean_object* v___x_3998_; 
lean_inc(v_indName_3988_);
v___x_3998_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4063_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4063_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4063_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
if (lean_obj_tag(v_a_3999_) == 5)
{
lean_object* v_val_4003_; uint8_t v_isRec_4004_; 
v_val_4003_ = lean_ctor_get(v_a_3999_, 0);
lean_inc_ref(v_val_4003_);
lean_dec_ref_known(v_a_3999_, 1);
v_isRec_4004_ = lean_ctor_get_uint8(v_val_4003_, sizeof(void*)*6);
if (v_isRec_4004_ == 0)
{
lean_object* v___x_4005_; lean_object* v___x_4007_; 
lean_dec_ref(v_val_4003_);
lean_dec(v_indName_3988_);
v___x_4005_ = lean_box(0);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4005_);
v___x_4007_ = v___x_4001_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
else
{
lean_object* v_toConstantVal_4009_; lean_object* v_numParams_4010_; lean_object* v_all_4011_; lean_object* v_numNested_4012_; lean_object* v_type_4013_; lean_object* v___x_4014_; 
lean_del_object(v___x_4001_);
v_toConstantVal_4009_ = lean_ctor_get(v_val_4003_, 0);
lean_inc_ref(v_toConstantVal_4009_);
v_numParams_4010_ = lean_ctor_get(v_val_4003_, 1);
lean_inc(v_numParams_4010_);
v_all_4011_ = lean_ctor_get(v_val_4003_, 3);
lean_inc(v_all_4011_);
v_numNested_4012_ = lean_ctor_get(v_val_4003_, 5);
lean_inc(v_numNested_4012_);
lean_dec_ref(v_val_4003_);
v_type_4013_ = lean_ctor_get(v_toConstantVal_4009_, 2);
lean_inc_ref(v_type_4013_);
lean_dec_ref(v_toConstantVal_4009_);
v___x_4014_ = l_Lean_Meta_isPropFormerType(v_type_4013_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4050_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4050_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4050_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
uint8_t v___x_4019_; 
v___x_4019_ = lean_unbox(v_a_4015_);
lean_dec(v_a_4015_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_4017_);
lean_inc_n(v_indName_3988_, 2);
v___x_4020_ = l_Lean_mkRecName(v_indName_3988_);
v___x_4021_ = l_Lean_mkBRecOnName(v_indName_3988_);
lean_inc(v_all_4011_);
v___x_4022_ = lean_array_mk(v_all_4011_);
lean_inc(v___x_4021_);
lean_inc_ref(v___x_4022_);
lean_inc(v_numParams_4010_);
lean_inc(v___x_4020_);
v___x_4023_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4020_, v_numParams_4010_, v___x_4022_, v___x_4021_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4044_; 
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4044_ == 0)
{
lean_object* v_unused_4045_; 
v_unused_4045_ = lean_ctor_get(v___x_4023_, 0);
lean_dec(v_unused_4045_);
v___x_4025_ = v___x_4023_;
v_isShared_4026_ = v_isSharedCheck_4044_;
goto v_resetjp_4024_;
}
else
{
lean_dec(v___x_4023_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4044_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v___x_4027_ = lean_unsigned_to_nat(0u);
v___x_4028_ = l_List_get_x21Internal___redArg(v___x_3997_, v_all_4011_, v___x_4027_);
lean_dec(v_all_4011_);
v___x_4029_ = lean_name_eq(v___x_4028_, v_indName_3988_);
lean_dec(v_indName_3988_);
lean_dec(v___x_4028_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; lean_object* v___x_4032_; 
lean_dec_ref(v___x_4022_);
lean_dec(v___x_4021_);
lean_dec(v___x_4020_);
lean_dec(v_numNested_4012_);
lean_dec(v_numParams_4010_);
v___x_4030_ = lean_box(0);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4030_);
v___x_4032_ = v___x_4025_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_del_object(v___x_4025_);
v___x_4034_ = lean_box(0);
v___x_4035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4012_, v___x_4020_, v___x_4021_, v_numParams_4010_, v___x_4022_, v___x_4027_, v___x_4034_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_numNested_4012_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4042_ == 0)
{
lean_object* v_unused_4043_; 
v_unused_4043_ = lean_ctor_get(v___x_4035_, 0);
lean_dec(v_unused_4043_);
v___x_4037_ = v___x_4035_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_dec(v___x_4035_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4034_);
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4034_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
else
{
return v___x_4035_;
}
}
}
}
else
{
lean_dec_ref(v___x_4022_);
lean_dec(v___x_4021_);
lean_dec(v___x_4020_);
lean_dec(v_numNested_4012_);
lean_dec(v_all_4011_);
lean_dec(v_numParams_4010_);
lean_dec(v_indName_3988_);
return v___x_4023_;
}
}
else
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
lean_dec(v_numNested_4012_);
lean_dec(v_all_4011_);
lean_dec(v_numParams_4010_);
lean_dec(v_indName_3988_);
v___x_4046_ = lean_box(0);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4046_);
v___x_4048_ = v___x_4017_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4046_);
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
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_numNested_4012_);
lean_dec(v_all_4011_);
lean_dec(v_numParams_4010_);
lean_dec(v_indName_3988_);
v_a_4051_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4014_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4014_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
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
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_dec(v_a_3999_);
lean_dec(v_indName_3988_);
v___x_4059_ = lean_box(0);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4059_);
v___x_4061_ = v___x_4001_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
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
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec(v_indName_3988_);
v_a_4064_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_3998_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_3998_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
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
lean_object* v_inheritedTraceOptions_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v_a_4081_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v_a_4096_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v_a_4101_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v_a_4106_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v_a_4118_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v_a_4123_; 
v_inheritedTraceOptions_4072_ = lean_ctor_get(v_toCold_3995_, 4);
lean_inc(v_indName_3988_);
v___f_4073_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4073_, 0, v_indName_3988_);
v___x_4074_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4075_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4076_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4072_, v_options_3994_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4192_ = l_Lean_trace_profiler;
v___x_4193_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3994_, v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; 
lean_dec_ref(v___f_4073_);
lean_inc(v_indName_3988_);
v___x_4194_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4259_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4197_ = v___x_4194_;
v_isShared_4198_ = v_isSharedCheck_4259_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4194_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4259_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
if (lean_obj_tag(v_a_4195_) == 5)
{
lean_object* v_val_4199_; uint8_t v_isRec_4200_; 
v_val_4199_ = lean_ctor_get(v_a_4195_, 0);
lean_inc_ref(v_val_4199_);
lean_dec_ref_known(v_a_4195_, 1);
v_isRec_4200_ = lean_ctor_get_uint8(v_val_4199_, sizeof(void*)*6);
if (v_isRec_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
lean_dec_ref(v_val_4199_);
lean_dec(v_indName_3988_);
v___x_4201_ = lean_box(0);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4201_);
v___x_4203_ = v___x_4197_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
else
{
lean_object* v_toConstantVal_4205_; lean_object* v_numParams_4206_; lean_object* v_all_4207_; lean_object* v_numNested_4208_; lean_object* v_type_4209_; lean_object* v___x_4210_; 
lean_del_object(v___x_4197_);
v_toConstantVal_4205_ = lean_ctor_get(v_val_4199_, 0);
lean_inc_ref(v_toConstantVal_4205_);
v_numParams_4206_ = lean_ctor_get(v_val_4199_, 1);
lean_inc(v_numParams_4206_);
v_all_4207_ = lean_ctor_get(v_val_4199_, 3);
lean_inc(v_all_4207_);
v_numNested_4208_ = lean_ctor_get(v_val_4199_, 5);
lean_inc(v_numNested_4208_);
lean_dec_ref(v_val_4199_);
v_type_4209_ = lean_ctor_get(v_toConstantVal_4205_, 2);
lean_inc_ref(v_type_4209_);
lean_dec_ref(v_toConstantVal_4205_);
v___x_4210_ = l_Lean_Meta_isPropFormerType(v_type_4209_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4246_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4246_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4246_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
uint8_t v___x_4215_; 
v___x_4215_ = lean_unbox(v_a_4211_);
lean_dec(v_a_4211_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
lean_del_object(v___x_4213_);
lean_inc_n(v_indName_3988_, 2);
v___x_4216_ = l_Lean_mkRecName(v_indName_3988_);
v___x_4217_ = l_Lean_mkBRecOnName(v_indName_3988_);
lean_inc(v_all_4207_);
v___x_4218_ = lean_array_mk(v_all_4207_);
lean_inc(v___x_4217_);
lean_inc_ref(v___x_4218_);
lean_inc(v_numParams_4206_);
lean_inc(v___x_4216_);
v___x_4219_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4216_, v_numParams_4206_, v___x_4218_, v___x_4217_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4240_; 
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4240_ == 0)
{
lean_object* v_unused_4241_; 
v_unused_4241_ = lean_ctor_get(v___x_4219_, 0);
lean_dec(v_unused_4241_);
v___x_4221_ = v___x_4219_;
v_isShared_4222_ = v_isSharedCheck_4240_;
goto v_resetjp_4220_;
}
else
{
lean_dec(v___x_4219_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4240_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4223_ = lean_unsigned_to_nat(0u);
v___x_4224_ = l_List_get_x21Internal___redArg(v___x_3997_, v_all_4207_, v___x_4223_);
lean_dec(v_all_4207_);
v___x_4225_ = lean_name_eq(v___x_4224_, v_indName_3988_);
lean_dec(v_indName_3988_);
lean_dec(v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4228_; 
lean_dec_ref(v___x_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v_numNested_4208_);
lean_dec(v_numParams_4206_);
v___x_4226_ = lean_box(0);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4226_);
v___x_4228_ = v___x_4221_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
return v___x_4228_;
}
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_del_object(v___x_4221_);
v___x_4230_ = lean_box(0);
v___x_4231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4208_, v___x_4216_, v___x_4217_, v_numParams_4206_, v___x_4218_, v___x_4223_, v___x_4230_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_numNested_4208_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4238_ == 0)
{
lean_object* v_unused_4239_; 
v_unused_4239_ = lean_ctor_get(v___x_4231_, 0);
lean_dec(v_unused_4239_);
v___x_4233_ = v___x_4231_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v___x_4231_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4230_);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4230_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
else
{
return v___x_4231_;
}
}
}
}
else
{
lean_dec_ref(v___x_4218_);
lean_dec(v___x_4217_);
lean_dec(v___x_4216_);
lean_dec(v_numNested_4208_);
lean_dec(v_all_4207_);
lean_dec(v_numParams_4206_);
lean_dec(v_indName_3988_);
return v___x_4219_;
}
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4244_; 
lean_dec(v_numNested_4208_);
lean_dec(v_all_4207_);
lean_dec(v_numParams_4206_);
lean_dec(v_indName_3988_);
v___x_4242_ = lean_box(0);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4242_);
v___x_4244_ = v___x_4213_;
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
lean_dec(v_numNested_4208_);
lean_dec(v_all_4207_);
lean_dec(v_numParams_4206_);
lean_dec(v_indName_3988_);
v_a_4247_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4210_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4210_);
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
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
lean_dec(v_a_4195_);
lean_dec(v_indName_3988_);
v___x_4255_ = lean_box(0);
if (v_isShared_4198_ == 0)
{
lean_ctor_set(v___x_4197_, 0, v___x_4255_);
v___x_4257_ = v___x_4197_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
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
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v_indName_3988_);
v_a_4260_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4194_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4194_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
goto v___jp_4125_;
}
}
else
{
goto v___jp_4125_;
}
v___jp_4078_:
{
lean_object* v___x_4082_; double v___x_4083_; double v___x_4084_; double v___x_4085_; double v___x_4086_; double v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4082_ = lean_io_mono_nanos_now();
v___x_4083_ = lean_float_of_nat(v___y_4080_);
v___x_4084_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4085_ = lean_float_div(v___x_4083_, v___x_4084_);
v___x_4086_ = lean_float_of_nat(v___x_4082_);
v___x_4087_ = lean_float_div(v___x_4086_, v___x_4084_);
v___x_4088_ = lean_box_float(v___x_4085_);
v___x_4089_ = lean_box_float(v___x_4087_);
v___x_4090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_a_4081_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4074_, v_hasTrace_3996_, v___x_4075_, v_options_3994_, v___x_4077_, v___y_4079_, v___f_4073_, v___x_4091_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
return v___x_4092_;
}
v___jp_4093_:
{
lean_object* v___x_4097_; 
v___x_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4096_);
v___y_4079_ = v___y_4095_;
v___y_4080_ = v___y_4094_;
v_a_4081_ = v___x_4097_;
goto v___jp_4078_;
}
v___jp_4098_:
{
lean_object* v___x_4102_; 
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_a_4101_);
v___y_4079_ = v___y_4100_;
v___y_4080_ = v___y_4099_;
v_a_4081_ = v___x_4102_;
goto v___jp_4078_;
}
v___jp_4103_:
{
lean_object* v___x_4107_; double v___x_4108_; double v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
v___x_4107_ = lean_io_get_num_heartbeats();
v___x_4108_ = lean_float_of_nat(v___y_4104_);
v___x_4109_ = lean_float_of_nat(v___x_4107_);
v___x_4110_ = lean_box_float(v___x_4108_);
v___x_4111_ = lean_box_float(v___x_4109_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4113_, 0, v_a_4106_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4074_, v_hasTrace_3996_, v___x_4075_, v_options_3994_, v___x_4077_, v___y_4105_, v___f_4073_, v___x_4113_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
return v___x_4114_;
}
v___jp_4115_:
{
lean_object* v___x_4119_; 
v___x_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4118_);
v___y_4104_ = v___y_4116_;
v___y_4105_ = v___y_4117_;
v_a_4106_ = v___x_4119_;
goto v___jp_4103_;
}
v___jp_4120_:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_a_4123_);
v___y_4104_ = v___y_4121_;
v___y_4105_ = v___y_4122_;
v_a_4106_ = v___x_4124_;
goto v___jp_4103_;
}
v___jp_4125_:
{
lean_object* v___x_4126_; lean_object* v_a_4127_; lean_object* v___x_4128_; uint8_t v___x_4129_; 
v___x_4126_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3992_);
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___x_4126_);
v___x_4128_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4129_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3994_, v___x_4128_);
if (v___x_4129_ == 0)
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3988_);
v___x_4131_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
if (lean_obj_tag(v_a_4132_) == 5)
{
lean_object* v_val_4133_; uint8_t v_isRec_4134_; 
v_val_4133_ = lean_ctor_get(v_a_4132_, 0);
lean_inc_ref(v_val_4133_);
lean_dec_ref_known(v_a_4132_, 1);
v_isRec_4134_ = lean_ctor_get_uint8(v_val_4133_, sizeof(void*)*6);
if (v_isRec_4134_ == 0)
{
lean_object* v___x_4135_; 
lean_dec_ref(v_val_4133_);
lean_dec(v_indName_3988_);
v___x_4135_ = lean_box(0);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v___x_4135_;
goto v___jp_4093_;
}
else
{
lean_object* v_toConstantVal_4136_; lean_object* v_numParams_4137_; lean_object* v_all_4138_; lean_object* v_numNested_4139_; lean_object* v_type_4140_; lean_object* v___x_4141_; 
v_toConstantVal_4136_ = lean_ctor_get(v_val_4133_, 0);
lean_inc_ref(v_toConstantVal_4136_);
v_numParams_4137_ = lean_ctor_get(v_val_4133_, 1);
lean_inc(v_numParams_4137_);
v_all_4138_ = lean_ctor_get(v_val_4133_, 3);
lean_inc(v_all_4138_);
v_numNested_4139_ = lean_ctor_get(v_val_4133_, 5);
lean_inc(v_numNested_4139_);
lean_dec_ref(v_val_4133_);
v_type_4140_ = lean_ctor_get(v_toConstantVal_4136_, 2);
lean_inc_ref(v_type_4140_);
lean_dec_ref(v_toConstantVal_4136_);
v___x_4141_ = l_Lean_Meta_isPropFormerType(v_type_4140_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; uint8_t v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = lean_unbox(v_a_4142_);
lean_dec(v_a_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
lean_inc_n(v_indName_3988_, 2);
v___x_4144_ = l_Lean_mkRecName(v_indName_3988_);
v___x_4145_ = l_Lean_mkBRecOnName(v_indName_3988_);
lean_inc(v_all_4138_);
v___x_4146_ = lean_array_mk(v_all_4138_);
lean_inc(v___x_4145_);
lean_inc_ref(v___x_4146_);
lean_inc(v_numParams_4137_);
lean_inc(v___x_4144_);
v___x_4147_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4144_, v_numParams_4137_, v___x_4146_, v___x_4145_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
lean_dec_ref_known(v___x_4147_, 1);
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = l_List_get_x21Internal___redArg(v___x_3997_, v_all_4138_, v___x_4148_);
lean_dec(v_all_4138_);
v___x_4150_ = lean_name_eq(v___x_4149_, v_indName_3988_);
lean_dec(v_indName_3988_);
lean_dec(v___x_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; 
lean_dec_ref(v___x_4146_);
lean_dec(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec(v_numNested_4139_);
lean_dec(v_numParams_4137_);
v___x_4151_ = lean_box(0);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v___x_4151_;
goto v___jp_4093_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = lean_box(0);
v___x_4153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4139_, v___x_4144_, v___x_4145_, v_numParams_4137_, v___x_4146_, v___x_4148_, v___x_4152_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_numNested_4139_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_dec_ref_known(v___x_4153_, 1);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v___x_4152_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4154_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4099_ = v___x_4130_;
v___y_4100_ = v_a_4127_;
v_a_4101_ = v_a_4154_;
goto v___jp_4098_;
}
}
}
else
{
lean_dec_ref(v___x_4146_);
lean_dec(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3988_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4155_; 
v_a_4155_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4147_, 1);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v_a_4155_;
goto v___jp_4093_;
}
else
{
lean_object* v_a_4156_; 
v_a_4156_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4147_, 1);
v___y_4099_ = v___x_4130_;
v___y_4100_ = v_a_4127_;
v_a_4101_ = v_a_4156_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v___x_4157_; 
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3988_);
v___x_4157_ = lean_box(0);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v___x_4157_;
goto v___jp_4093_;
}
}
else
{
lean_object* v_a_4158_; 
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3988_);
v_a_4158_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4141_, 1);
v___y_4099_ = v___x_4130_;
v___y_4100_ = v_a_4127_;
v_a_4101_ = v_a_4158_;
goto v___jp_4098_;
}
}
}
else
{
lean_object* v___x_4159_; 
lean_dec(v_a_4132_);
lean_dec(v_indName_3988_);
v___x_4159_ = lean_box(0);
v___y_4094_ = v___x_4130_;
v___y_4095_ = v_a_4127_;
v_a_4096_ = v___x_4159_;
goto v___jp_4093_;
}
}
else
{
lean_object* v_a_4160_; 
lean_dec(v_indName_3988_);
v_a_4160_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4131_, 1);
v___y_4099_ = v___x_4130_;
v___y_4100_ = v_a_4127_;
v_a_4101_ = v_a_4160_;
goto v___jp_4098_;
}
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3988_);
v___x_4162_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
if (lean_obj_tag(v_a_4163_) == 5)
{
lean_object* v_val_4164_; uint8_t v_isRec_4165_; 
v_val_4164_ = lean_ctor_get(v_a_4163_, 0);
lean_inc_ref(v_val_4164_);
lean_dec_ref_known(v_a_4163_, 1);
v_isRec_4165_ = lean_ctor_get_uint8(v_val_4164_, sizeof(void*)*6);
if (v_isRec_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec_ref(v_val_4164_);
lean_dec(v_indName_3988_);
v___x_4166_ = lean_box(0);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v___x_4166_;
goto v___jp_4115_;
}
else
{
lean_object* v_toConstantVal_4167_; lean_object* v_numParams_4168_; lean_object* v_all_4169_; lean_object* v_numNested_4170_; lean_object* v_type_4171_; lean_object* v___x_4172_; 
v_toConstantVal_4167_ = lean_ctor_get(v_val_4164_, 0);
lean_inc_ref(v_toConstantVal_4167_);
v_numParams_4168_ = lean_ctor_get(v_val_4164_, 1);
lean_inc(v_numParams_4168_);
v_all_4169_ = lean_ctor_get(v_val_4164_, 3);
lean_inc(v_all_4169_);
v_numNested_4170_ = lean_ctor_get(v_val_4164_, 5);
lean_inc(v_numNested_4170_);
lean_dec_ref(v_val_4164_);
v_type_4171_ = lean_ctor_get(v_toConstantVal_4167_, 2);
lean_inc_ref(v_type_4171_);
lean_dec_ref(v_toConstantVal_4167_);
v___x_4172_ = l_Lean_Meta_isPropFormerType(v_type_4171_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; uint8_t v___x_4174_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4172_, 1);
v___x_4174_ = lean_unbox(v_a_4173_);
lean_dec(v_a_4173_);
if (v___x_4174_ == 0)
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_inc_n(v_indName_3988_, 2);
v___x_4175_ = l_Lean_mkRecName(v_indName_3988_);
v___x_4176_ = l_Lean_mkBRecOnName(v_indName_3988_);
lean_inc(v_all_4169_);
v___x_4177_ = lean_array_mk(v_all_4169_);
lean_inc(v___x_4176_);
lean_inc_ref(v___x_4177_);
lean_inc(v_numParams_4168_);
lean_inc(v___x_4175_);
v___x_4178_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4175_, v_numParams_4168_, v___x_4177_, v___x_4176_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
lean_dec_ref_known(v___x_4178_, 1);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = l_List_get_x21Internal___redArg(v___x_3997_, v_all_4169_, v___x_4179_);
lean_dec(v_all_4169_);
v___x_4181_ = lean_name_eq(v___x_4180_, v_indName_3988_);
lean_dec(v_indName_3988_);
lean_dec(v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec_ref(v___x_4177_);
lean_dec(v___x_4176_);
lean_dec(v___x_4175_);
lean_dec(v_numNested_4170_);
lean_dec(v_numParams_4168_);
v___x_4182_ = lean_box(0);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v___x_4182_;
goto v___jp_4115_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4183_ = lean_box(0);
v___x_4184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4170_, v___x_4175_, v___x_4176_, v_numParams_4168_, v___x_4177_, v___x_4179_, v___x_4183_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_numNested_4170_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_dec_ref_known(v___x_4184_, 1);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v___x_4183_;
goto v___jp_4115_;
}
else
{
lean_object* v_a_4185_; 
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4121_ = v___x_4161_;
v___y_4122_ = v_a_4127_;
v_a_4123_ = v_a_4185_;
goto v___jp_4120_;
}
}
}
else
{
lean_dec_ref(v___x_4177_);
lean_dec(v___x_4176_);
lean_dec(v___x_4175_);
lean_dec(v_numNested_4170_);
lean_dec(v_all_4169_);
lean_dec(v_numParams_4168_);
lean_dec(v_indName_3988_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4186_; 
v_a_4186_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v_a_4186_;
goto v___jp_4115_;
}
else
{
lean_object* v_a_4187_; 
v_a_4187_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4187_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4121_ = v___x_4161_;
v___y_4122_ = v_a_4127_;
v_a_4123_ = v_a_4187_;
goto v___jp_4120_;
}
}
}
else
{
lean_object* v___x_4188_; 
lean_dec(v_numNested_4170_);
lean_dec(v_all_4169_);
lean_dec(v_numParams_4168_);
lean_dec(v_indName_3988_);
v___x_4188_ = lean_box(0);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v___x_4188_;
goto v___jp_4115_;
}
}
else
{
lean_object* v_a_4189_; 
lean_dec(v_numNested_4170_);
lean_dec(v_all_4169_);
lean_dec(v_numParams_4168_);
lean_dec(v_indName_3988_);
v_a_4189_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4172_, 1);
v___y_4121_ = v___x_4161_;
v___y_4122_ = v_a_4127_;
v_a_4123_ = v_a_4189_;
goto v___jp_4120_;
}
}
}
else
{
lean_object* v___x_4190_; 
lean_dec(v_a_4163_);
lean_dec(v_indName_3988_);
v___x_4190_ = lean_box(0);
v___y_4116_ = v___x_4161_;
v___y_4117_ = v_a_4127_;
v_a_4118_ = v___x_4190_;
goto v___jp_4115_;
}
}
else
{
lean_object* v_a_4191_; 
lean_dec(v_indName_3988_);
v_a_4191_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4162_, 1);
v___y_4121_ = v___x_4161_;
v___y_4122_ = v_a_4127_;
v_a_4123_ = v_a_4191_;
goto v___jp_4120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_mkBRecOn(v_indName_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4275_, lean_object* v___x_4276_, lean_object* v___x_4277_, lean_object* v___x_4278_, lean_object* v___x_4279_, lean_object* v_inst_4280_, lean_object* v_R_4281_, lean_object* v_a_4282_, lean_object* v_b_4283_, lean_object* v_c_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v___x_4290_; 
v___x_4290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4275_, v___x_4276_, v___x_4277_, v___x_4278_, v___x_4279_, v_a_4282_, v_b_4283_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
return v___x_4290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4291_, lean_object* v___x_4292_, lean_object* v___x_4293_, lean_object* v___x_4294_, lean_object* v___x_4295_, lean_object* v_inst_4296_, lean_object* v_R_4297_, lean_object* v_a_4298_, lean_object* v_b_4299_, lean_object* v_c_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4291_, v___x_4292_, v___x_4293_, v___x_4294_, v___x_4295_, v_inst_4296_, v_R_4297_, v_a_4298_, v_b_4299_, v_c_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v_upperBound_4291_);
return v_res_4306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_unsigned_to_nat(2304625798u);
v___x_4353_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4354_ = l_Lean_Name_num___override(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4357_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4358_ = l_Lean_Name_str___override(v___x_4357_, v___x_4356_);
return v___x_4358_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4361_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4362_ = l_Lean_Name_str___override(v___x_4361_, v___x_4360_);
return v___x_4362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = lean_unsigned_to_nat(2u);
v___x_4364_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4365_ = l_Lean_Name_num___override(v___x_4364_, v___x_4363_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4367_; uint8_t v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4367_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4368_ = 0;
v___x_4369_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4370_ = l_Lean_registerTraceClass(v___x_4367_, v___x_4368_, v___x_4369_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4372_;
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
